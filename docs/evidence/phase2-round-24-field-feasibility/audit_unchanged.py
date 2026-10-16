from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import subprocess

ROOT = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
PARENT = '088b48f5ede5e1f072e3d00540b616b28c6e4bc4'
PRIOR = ROOT / 'docs/evidence/phase2-round-23-warp-calibration'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def verify_git_blobs(paths, revision):
    raw = subprocess.check_output(['git', 'cat-file', '--batch'], cwd=ROOT,
        input=''.join(revision + ':' + p + '\n' for p in paths).encode())
    buf = io.BytesIO(raw)
    for p in paths:
        header = buf.readline().decode().strip().split()
        assert len(header) == 3 and header[1] == 'blob', p
        blob = buf.read(int(header[2]))
        assert buf.read(1) == b'\n'
        assert hashlib.sha256(blob).hexdigest() == sha(ROOT / p), p
    assert not buf.read()

assert git('rev-parse', 'HEAD').decode().strip() == PARENT
prior = json.loads((PRIOR / 'receipt.json').read_text())
assert sha(PRIOR / 'receipt.json') == '6a454dfdb414a69f0fd0aebf75256618c9ad1e0caac979cedb633ad91561afd3'
for p, h in prior['source_hashes'].items():
    assert sha(ROOT / p) == h, p
leaves = [p for p in prior['source_hashes']
          if p.startswith('RicciFlowSharpEstimate/') and p.endswith('.lean')]
physical = {str(p.relative_to(ROOT)) for p in (ROOT / 'RicciFlowSharpEstimate').rglob('*.lean')}
assert len(leaves) == 357 and physical == set(leaves)
for r in prior['commands']:
    assert r['exit_code'] == 0
    assert sha(PRIOR / (r['label'] + '.txt')) == r['output_sha256'], r['label']
assert len(prior['source_hashes']) == 362 and len(prior['commands']) == 363

source_record = json.loads((S / 'AffineFieldChecks.completion.json').read_text())
lean = Path(source_record['command'][0])
env = {'platform': platform.platform(),
       'lean_version': subprocess.check_output([str(lean), '--version'], text=True).strip(),
       'lean_binary_sha256': sha(lean), 'dependencies': {}}
for name in prior['dependencies']:
    package = ROOT / '.lake/packages' / name
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=package, text=True).strip()
    clean = not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                        cwd=package, text=True).strip()
    env['dependencies'][name] = {'revision': revision, 'tracked_sources_clean': clean}
for key in env:
    assert env[key] == prior[key], key
options = next(ast.literal_eval(n.value) for n in ast.parse((ROOT / 'scripts/check_native.py').read_text()).body
    if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'OPTIONS' for t in n.targets))
assert [o for o in source_record['command'] if o.startswith('-D')] == options
env.update({'lean_binary_path': str(lean), 'options': options,
            'unchanged_accepted_native_inputs': len(prior['source_hashes']),
            'unchanged_accepted_command_output_bindings': len(prior['commands']),
            'unchanged_canonical_modules': len(leaves),
            'fresh_canonical_build_or_full_suite_recomputation': False,
            'parent_revision': PARENT, 'parent_receipt_path': str(PRIOR / 'receipt.json'),
            'parent_receipt_sha256': sha(PRIOR / 'receipt.json')})
(S / 'current-environment.json').write_text(json.dumps(env, indent=2) + '\n')

phase1 = git('ls-tree', '-r', '--name-only', '721fd81', 'RicciFlowSharpEstimate').decode().splitlines()
assert len(phase1) == 149 and set(phase1) <= set(leaves)
verify_git_blobs(phase1, '721fd81')
baseline = json.loads((ROOT / '.references/phase2-unrestricted-20261012/preservation-receipt.json').read_text())
for p, h in baseline['preserved_phase1_loop_hashes'].items():
    assert sha(ROOT / p) == h, p
papers = {p: h for p, h in baseline['preserved_artifact_hashes'].items() if p.startswith('paper/')}
for p, h in papers.items():
    assert sha(ROOT / p) == h, p
assert sha(ROOT / '.references/TASK.md') == baseline['preserved_artifact_hashes']['.references/TASK.md']
assert sha(ROOT / '.references/phase2-unrestricted-20261012/TASK.md') == baseline['phase2_task_sha256']
evidence = git('ls-tree', '-r', '--name-only', PARENT, 'docs/evidence').decode().splitlines()
verify_git_blobs(evidence, PARENT)
immutable = (ROOT / '.humanize/rlcr/2026-10-12_19-57-48/goal-tracker.md').read_bytes().split(b'## MUTABLE SECTION')[0]
assert hashlib.sha256(immutable).hexdigest() == '3222e336ce7edb57d5cd4794bbc6c0c43ec833a595d69254214c98a8e6ded6e1'
kb = sha(ROOT / '.humanize/bitlesson.md')
assert kb == '48215551a10642e35fca9e2bcbb8dfa5fba713b266a62d43c5721903e1e83855'
restart = Path('/home/ubuntu/.local/state/rfse-route-recovery-20261015')
historical = json.loads((restart / 'rounds-before.json').read_text())
mutable = {'.humanize/rlcr/2026-10-12_19-57-48/goal-tracker.md',
           '.humanize/rlcr/2026-10-12_19-57-48/tasks.json'}
historical = {p: h for p, h in historical.items() if p not in mutable}
for p, h in historical.items():
    assert sha(ROOT / p) == h, p
before = json.loads((restart / 'source-before.json').read_text())
intentional = {'RicciFlowSharpEstimate.lean', 'scripts/check_native.py',
               'docs/mathematical-status.md', 'docs/theorem-map.md',
               'docs/research/phase2-unrestricted.md', 'docs/verification.md'}
old_deltas = {p for p, h in before.items() if sha(ROOT / p) != h}
assert old_deltas <= intentional, old_deltas - intentional
report = {'phase1_status': 'COMPLETE; preserved', 'phase2_status': 'OPEN',
          'parent_revision': PARENT, 'unchanged_canonical_modules': len(leaves),
          'canonical_source_changes': [], 'new_canonical_declarations': 0,
          'unchanged_phase1_modules': len(phase1),
          'unchanged_phase1_workflow_files': len(baseline['preserved_phase1_loop_hashes']),
          'paper_sha256': papers, 'both_tasks_unchanged': True,
          'pins_sha256': {p: sha(ROOT / p) for p in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']},
          'unchanged_prior_evidence_files': len(evidence),
          'immutable_tracker_prefix_sha256': hashlib.sha256(immutable).hexdigest(),
          'bitlesson_sha256': kb, 'unchanged_pre_restart_round_files': len(historical),
          'pre_restart_source_and_evidence_bindings': len(before),
          'intentional_existing_file_deltas': sorted(old_deltas),
          'current_environment_path': str(S / 'current-environment.json'),
          'current_environment_sha256': sha(S / 'current-environment.json'),
          'audit_source_path': str(Path(__file__).resolve()), 'audit_source_sha256': sha(__file__)}
(S / 'preservation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'native_inputs': len(prior['source_hashes']), 'old_outputs': len(prior['commands']),
                  'canonical_modules': len(leaves), 'prior_evidence': len(evidence),
                  'phase1_modules': len(phase1), 'workflow': report['unchanged_phase1_workflow_files'],
                  'historical_round_files': len(historical), 'all_bindings_match': True}))
