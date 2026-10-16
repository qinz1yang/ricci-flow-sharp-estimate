"""Retain the successful native prefix and repair only signature name scopes."""
from pathlib import Path
import ast
import datetime
import fcntl
import hashlib
import json
import platform
import shutil
import subprocess

R = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
O = R / 'docs/evidence/phase2-round-26-strict-pinching'
CHECKER = R / 'scripts/check_native.py'
OLD = S / 'checker-before-signature-scope-fix.py'
PREFIX = S / 'native-round26-progress.json'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def values_of(text):
    values = {}
    def literal(n):
        if isinstance(n, ast.Constant): return n.value
        if isinstance(n, ast.List): return [literal(x) for x in n.elts]
        if isinstance(n, ast.Name): return values[n.id]
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Add):
            return literal(n.left) + literal(n.right)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute):
            assert n.func.attr == 'lstrip' and not n.keywords
            return literal(n.func.value).lstrip(*[literal(x) for x in n.args])
        raise ValueError(ast.dump(n))
    for n in ast.parse(text).body:
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            if n.targets[0].id in {'MODULES', 'OPTIONS', 'SELECTOR', 'LINT_DRIVER',
                                   'AXIOM_DRIVER', 'SIGNATURE_DRIVER'}:
                values[n.targets[0].id] = literal(n.value)
    return values

def policy(text, omitted):
    t = ast.parse(text)
    for n in t.body:
        if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name):
            if n.targets[0].id in omitted: n.value = ast.Constant('inventory omitted')
    return ast.dump(t, include_attributes=False)

before = OLD.read_text()
after = CHECKER.read_text()
assert policy(before, {'SIGNATURE_DRIVER'}) == policy(after, {'SIGNATURE_DRIVER'})
parent = subprocess.check_output(['git', 'show', 'HEAD:scripts/check_native.py'], cwd=R, text=True)
assert policy(parent, {'MODULES', 'SELECTOR', 'SIGNATURE_DRIVER'}) == policy(
    after, {'MODULES', 'SELECTOR', 'SIGNATURE_DRIVER'})
v = values_of(after)
old = values_of(before)
assert all(v[k] == old[k] for k in v if k != 'SIGNATURE_DRIVER')
p = json.loads(PREFIX.read_text())
assert p['source_hashes']['scripts/check_native.py'] == sha(OLD)
hashes = {q: sha(R / q) for q in p['source_hashes']}
assert all(hashes[q] == h for q, h in p['source_hashes'].items()
           if q != 'scripts/check_native.py')
assert len(hashes) == 365
records = p['commands']
assert len(records) == 366 and records[-1]['label'] == 'signatures'
assert records[-1]['exit_code'] != 0
for c in records:
    assert sha(O / (c['label'] + '.txt')) == c['output_sha256'], c['label']
for c in records[:-1]:
    assert c['exit_code'] == 0, c['label']
    if c['label'] in {m.rsplit('.', 1)[1].lower() for m in v['MODULES']} | {'linters'}:
        assert not (O / (c['label'] + '.txt')).read_bytes(), c['label']
for label, key in [('linters', 'LINT_DRIVER'), ('axioms', 'AXIOM_DRIVER')]:
    c = next(c for c in records if c['label'] == label)
    assert c['driver_sha256'] == hashlib.sha256(v[key].encode()).hexdigest()
shutil.copy2(PREFIX, S / 'native-prefix-before-signature-repair.json')
shutil.copy2(O / 'signatures.txt', S / 'signature-scope-development.txt')
driver = S / 'FinalSignatures.lean'
driver.write_text(v['SIGNATURE_DRIVER'])
cmd = ['lake', 'env', 'lean', *v['OPTIONS'], str(driver)]
with (R / '.lake/rfse-root-writer.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    result = subprocess.run(cmd, cwd=R, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(O / 'signatures.txt').write_text(result.stdout)
record = {'label': 'signatures', 'command': cmd, 'exit_code': result.returncode,
          'output_sha256': sha(O / 'signatures.txt'), 'driver_sha256': sha(driver)}
if result.returncode or 'warning:' in result.stdout or 'error:' in result.stdout:
    print(result.stdout, end='')
    raise RuntimeError('Corrected final signature driver failed')
commands = records[:-1] + [record]
assert hashes == {q: sha(R / q) for q in hashes}
prior = json.loads((R / 'docs/evidence/phase2-round-22-pinching-safety/receipt.json').read_text())
lean = Path((O / 'lean-path.txt').read_text().strip())
assert sha(lean) == prior['lean_binary_sha256']
dependencies = {}
manifest = json.loads((R / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    path = R / manifest['packagesDir'] / package['name']
    revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    assert revision == package['rev']
    subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD'], check=True)
    dependencies[package['name']] = {'revision': revision, 'tracked_sources_clean': True}
assert dependencies == prior['dependencies']
receipt = {
    'source_hashes': hashes, 'platform': platform.platform(),
    'lean_version': (O / 'lean-version.txt').read_text().strip(),
    'lean_binary_sha256': sha(lean), 'dependencies': dependencies, 'commands': commands,
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'declaration_linters': ['unusedArguments', 'simpNF', 'synTaut'],
    'defLemma_replacement': 'Native getConstInfo/Meta.isProp inspection of declaration kinds',
    'independent_review': 'pending outer review; native evidence alone is not suite acceptance',
    'execution_orchestration': {
        'path': str(Path(__file__).resolve()), 'sha256': sha(__file__),
        'successful_prefix_records': 365,
        'prefix_path': str(S / 'native-prefix-before-signature-repair.json'),
        'prefix_sha256': sha(S / 'native-prefix-before-signature-repair.json'),
        'prefix_runner_path': str(S / 'native_round26.py'),
        'prefix_runner_sha256': sha(S / 'native_round26.py'),
        'initial_checker_path': str(OLD), 'initial_checker_sha256': sha(OLD),
        'initial_checker_differs_only_in_signature_inventory': True,
        'linters_and_axiom_literal_drivers_identical_to_final_checker': True,
        'original_entry_point_success_claimed': False,
        'obsolete_signature_cancellation_path': str(S / 'obsolete-signature-cancellation.json'),
        'obsolete_signature_cancellation_sha256': sha(S / 'obsolete-signature-cancellation.json'),
        'development_kind': 'Root canceled the obsolete signature command after its namespace inventory was corrected; this was not a mathematical source/compiler rejection.',
        'signature_scope_failure_path': str(S / 'signature-scope-development.txt'),
        'signature_scope_failure_sha256': sha(S / 'signature-scope-development.txt'),
        'scope': 'All native commands/options/diagnostic gates match the final checker; its five new signature queries receive their namespace scopes. The 365 actual successful prefix records are retained, only the corrected literal signature driver is fresh. No wall timeout or Lean option is added.',
        'writer_lock': '.lake/rfse-root-writer.lock',
    },
}
(O / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
(S / 'final-checker-policy-audit.json').write_text(json.dumps({
    'final_checker_sha256': sha(CHECKER),
    'policy_ast_equal_to_parent_outside_inventories': True,
    'prefix_checker_differs_only_in_signature_inventory': True,
    'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}, indent=2) + '\n')
print('Final native gate passed with retained successful prefix: 365 inputs, 366 outputs', flush=True)
