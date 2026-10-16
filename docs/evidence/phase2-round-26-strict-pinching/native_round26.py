"""Root orchestration of the inspected native gate, without its wall timeout.

The checker entry point is not executed. Inventories/options/drivers are
reconstructed from literal AST expressions. Commands, reuse checks and all
diagnostic requirements are identical to the inspected checker.
"""
import ast
import datetime
import fcntl
import hashlib
import json
import platform
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path('/home/ubuntu/projects/rfse')
SCRATCH = Path(__file__).parent
OUT = ROOT / 'docs/evidence/phase2-round-26-strict-pinching'
PRIOR = ROOT / 'docs/evidence/phase2-round-22-pinching-safety/receipt.json'
CHECKER = ROOT / 'scripts/check_native.py'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

values = {}
def literal(node):
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.List):
        return [literal(x) for x in node.elts]
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return literal(node.left) + literal(node.right)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        assert node.func.attr == 'lstrip' and not node.keywords
        return literal(node.func.value).lstrip(*[literal(a) for a in node.args])
    raise ValueError(ast.dump(node))

tree = ast.parse(CHECKER.read_text())
keys = {'MODULES', 'OPTIONS', 'SELECTOR', 'LINT_DRIVER', 'AXIOM_DRIVER', 'SIGNATURE_DRIVER'}
for node in tree.body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1:
        target = node.targets[0]
        if isinstance(target, ast.Name) and target.id in keys:
            values[target.id] = literal(node.value)
assert keys == set(values)
def policy(text):
    parsed = ast.parse(text)
    for node in parsed.body:
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in {'MODULES', 'SELECTOR', 'SIGNATURE_DRIVER'}:
                node.value = ast.Constant('inventory omitted')
    return ast.dump(parsed, include_attributes=False)
parent_checker = subprocess.check_output(
    ['git', 'show', 'HEAD:scripts/check_native.py'], cwd=ROOT, text=True)
assert policy(parent_checker) == policy(CHECKER.read_text())
(SCRATCH / 'checker-policy-audit.json').write_text(json.dumps({
    'checker_sha256': sha(CHECKER), 'policy_ast_equal_outside_inventories': True,
    'changed_inventories': ['MODULES', 'SELECTOR', 'SIGNATURE_DRIVER'],
    'checker_entry_point_executed': False,
}, indent=2) + '\n')

modules = values['MODULES']
options = values['OPTIONS']
physical = sorted(str(p.relative_to(ROOT)).removesuffix('.lean').replace('/', '.')
                  for p in (ROOT / 'RicciFlowSharpEstimate').rglob('*.lean'))
imports = re.findall(r'^import (RicciFlowSharpEstimate\S+)$',
                     (ROOT / 'RicciFlowSharpEstimate.lean').read_text(), re.M)
assert sorted(modules) == physical == sorted(imports)
assert len(modules) == len(set(modules)) == 360
inputs = [ROOT / p for p in ['RicciFlowSharpEstimate.lean', 'lakefile.toml',
          'lean-toolchain', 'lake-manifest.json', 'scripts/check_native.py']]
inputs += [ROOT / (m.replace('.', '/') + '.lean') for m in modules]
hashes = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
prior = json.loads(PRIOR.read_text())
prior_hash = sha(PRIOR)
prior_modules = [p for p in prior['source_hashes']
                 if p.startswith('RicciFlowSharpEstimate/') and p.endswith('.lean')]
assert len(prior_modules) == 354
for p in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json'] + prior_modules:
    assert hashes[p] == prior['source_hashes'][p], p
assert not OUT.exists(), 'Do not overwrite a native attempt or accepted evidence'
OUT.mkdir()
commands = []
def progress():
    (SCRATCH / 'native-round26-progress.json').write_text(json.dumps({
        'source_hashes': hashes, 'commands': commands,
        'updated_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    }, indent=2) + '\n')

def run(label, command, silent=False):
    print('Native: ' + label, flush=True)
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    raw = OUT / (label + '.txt')
    raw.write_text(result.stdout)
    commands.append({'label': label, 'command': command, 'exit_code': result.returncode,
                     'output_sha256': sha(raw)})
    progress()
    if (result.returncode or 'warning:' in result.stdout or 'error:' in result.stdout
            or (silent and result.stdout.strip())):
        print(result.stdout, end='', flush=True)
        raise RuntimeError('Native check failed: ' + label)
    return result.stdout

with (ROOT / '.lake/rfse-root-writer.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    run('root-build', ['lake', 'build'])
    version = run('lean-version', ['lake', 'env', 'lean', '--version'])
    lean_path = Path(run('lean-path', ['lake', 'env', 'which', 'lean']).strip())
    dependencies = {}
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        path = ROOT / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(
            ['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        assert revision == package['rev'], package['name']
        subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD'], check=True)
        dependencies[package['name']] = {'revision': revision, 'tracked_sources_clean': True}
    assert prior['lean_binary_sha256'] == sha(lean_path)
    assert prior['dependencies'] == dependencies
    reusable = {}
    for entry in prior['commands']:
        command = entry['command']
        if not command:
            continue
        source = Path(command[-1])
        if not source.is_relative_to(ROOT):
            continue
        relative = str(source.relative_to(ROOT))
        if relative not in prior_modules:
            continue
        assert [x for x in command if x.startswith('-D')] == options
        raw = PRIOR.parent / (entry['label'] + '.txt')
        assert entry['exit_code'] == 0 and sha(raw) == entry['output_sha256']
        assert not raw.read_text().strip()
        reusable[relative] = (entry, raw)
    assert len(reusable) == 354
    for module in modules:
        relative = module.replace('.', '/') + '.lean'
        if relative in reusable:
            entry, raw = reusable[relative]
            shutil.copyfile(raw, OUT / (entry['label'] + '.txt'))
            commands.append({**entry, 'reused_from': {
                'receipt': str(PRIOR.relative_to(ROOT)), 'sha256': prior_hash}})
            continue
        run(module.rsplit('.', 1)[1].lower(),
            ['lake', 'env', 'lean', *options, str(ROOT / relative)], silent=True)
    with tempfile.TemporaryDirectory(prefix='math-target-', dir=SCRATCH) as scratch:
        for label, key, silent in [('linters', 'LINT_DRIVER', True),
                                  ('axioms', 'AXIOM_DRIVER', False),
                                  ('signatures', 'SIGNATURE_DRIVER', False)]:
            path = Path(scratch) / (label.capitalize() + '.lean')
            path.write_text(values[key])
            run(label, ['lake', 'env', 'lean', *options, str(path)], silent)
            commands[-1]['driver_sha256'] = sha(path)
            progress()
    assert hashes == {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    labels = [c['label'] for c in commands]
    assert len(labels) == len(set(labels)) == 366
    receipt = {
        'source_hashes': hashes, 'platform': platform.platform(),
        'lean_version': version.strip(), 'lean_binary_sha256': sha(lean_path),
        'dependencies': dependencies, 'commands': commands,
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'declaration_linters': ['unusedArguments', 'simpNF', 'synTaut'],
        'defLemma_replacement': 'Native getConstInfo/Meta.isProp inspection of declaration kinds',
        'independent_review': 'pending outer review; native evidence alone is not suite acceptance',
        'execution_orchestration': {
            'path': str(Path(__file__).resolve()), 'sha256': sha(__file__),
            'checker_entry_point_executed': False,
            'scope': 'Root executes identical native commands, literal diagnostic drivers, reuse and fail-fast requirements without the helper external 180s wall timeout; Lean options and all diagnostics unchanged',
            'writer_lock': '.lake/rfse-root-writer.lock',
        },
    }
    (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Native gate passed: ' + str(OUT), flush=True)
