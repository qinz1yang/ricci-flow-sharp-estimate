from pathlib import Path
import ast
import datetime
import fcntl
import hashlib
import json
import os
import subprocess

ROOT = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

modules = ['FreeTraceChecks']
records = []
for name in modules:
    r = json.loads((S / (name + '.completion.json')).read_text())
    assert r['exit_code'] == 0
    assert sha(S / (name + '.lean')) == r['source_sha256']
    assert sha(S / 'imports' / (name + '.lean')) == r['source_sha256']
    assert sha(S / (name + '.txt')) == r['output_sha256']
    assert not (S / (name + '.txt')).read_bytes()
    records.append({**r, 'name': name, 'source_path': str(S / (name + '.lean')),
                    'compiled_source_path': str(S / 'imports' / (name + '.lean')),
                    'olean_sha256': sha(S / 'imports' / (name + '.olean'))})
options = next(ast.literal_eval(n.value)
    for n in ast.parse((ROOT / 'scripts/check_native.py').read_text()).body
    if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'OPTIONS'
                                       for t in n.targets))
for r in records:
    assert [o for o in r['command'] if o.startswith('-D')] == options

results = []
with (ROOT / '.lake/rfse-root-writer.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=ROOT, text=True).strip()
    lp = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    env = os.environ.copy()
    env['LEAN_PATH'] = str(S / 'imports') + ':' + lp
    for name, silent in [('ResearchLinters', True), ('ResearchAxioms', False)]:
        source = S / (name + '.lean')
        command = [lean, *options, str(source)]
        r = subprocess.run(command, cwd=ROOT, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        raw = S / (name + '.txt')
        raw.write_text(r.stdout)
        rec = {'name': name, 'command': command, 'LEAN_PATH': env['LEAN_PATH'],
               'exit_code': r.returncode, 'source_path': str(source),
               'source_sha256': sha(source), 'output_path': str(raw),
               'output_sha256': sha(raw),
               'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
        results.append(rec)
        (S / 'diagnostics-progress.json').write_text(json.dumps(results, indent=2) + '\n')
        assert r.returncode == 0 and 'warning:' not in r.stdout and 'error:' not in r.stdout, r.stdout
        assert not silent or not r.stdout.strip(), r.stdout
        print(name + ': exit0' + ('; silent' if silent else '; explicit types/axioms recorded'), flush=True)
    for name, rec in zip(modules, records):
        assert sha(S / (name + '.lean')) == rec['source_sha256']
        assert sha(S / 'imports' / (name + '.olean')) == rec['olean_sha256']

(S / 'research-native.json').write_text(json.dumps({
    'scope': 'One private free-trace diagnostic only; no new canonical theorem or bound; mainline STALLED',
    'modules': records, 'diagnostics': results,
    'runner_path': str(Path(__file__).resolve()), 'runner_sha256': sha(__file__),
    'writer_lock': '.lake/rfse-root-writer.lock',
    'parent_source_gate': 'Round26 canonical gate and accepted delta review reused unchanged; no new root build or old private-proof rerun',
}, indent=2) + '\n')
