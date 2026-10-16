from pathlib import Path
import ast
import datetime
import fcntl
import hashlib
import json
import subprocess
import sys

R = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
P = S / 'SlopeGapChecks.lean'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
opts = next(ast.literal_eval(n.value) for n in ast.parse((R / 'scripts/check_native.py').read_text()).body
    if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'OPTIONS' for t in n.targets))
before = sha(P)
cmd = ['lake', 'env', 'lean', *opts, str(P)]
with (R / '.lake/rfse-root-writer.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=R, text=True).strip()
    assert 'math-target-' not in lean_path and str(S / 'imports') not in lean_path
    result = subprocess.run(cmd, cwd=R, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
out = S / 'SlopeGapChecks.txt'
out.write_text(result.stdout)
assert before == sha(P)
record = {'command': cmd, 'exit_code': result.returncode, 'source_sha256': before,
    'output_sha256': sha(out), 'canonical_imports_without_scratch_overlay': True,
    'LEAN_PATH': lean_path,
    'writer_lock': '.lake/rfse-root-writer.lock',
    'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
(S / 'SlopeGapChecks.completion.json').write_text(json.dumps(record, indent=2) + '\n')
print(result.stdout, end='')
if result.returncode or result.stdout.strip():
    raise RuntimeError('Canonical consumer must pass silently')
print('Canonical consumer passed silently', flush=True)
