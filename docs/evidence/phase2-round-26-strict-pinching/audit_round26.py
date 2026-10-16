from pathlib import Path
import hashlib
import io
import json
import subprocess

ROOT = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
PARENT = '978eec876a9ed7ee815bd0d936d395a53a8ce91c'
OUT = ROOT / 'docs/evidence/phase2-round-26-strict-pinching'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def check_blobs(paths, revision):
    if not paths:
        return
    data = subprocess.check_output(
        ['git', 'cat-file', '--batch'], cwd=ROOT,
        input=''.join(revision + ':' + p + '\n' for p in paths).encode())
    buf = io.BytesIO(data)
    for p in paths:
        head = buf.readline().decode().split()
        assert len(head) == 3 and head[1] == 'blob', p
        b = buf.read(int(head[2]))
        assert buf.read(1) == b'\n'
        assert hashlib.sha256(b).hexdigest() == sha(ROOT / p), p
    assert not buf.read()

assert git('rev-parse', 'HEAD').decode().strip() == PARENT
parent_leaves = git('ls-tree', '-r', '--name-only', PARENT,
                    'RicciFlowSharpEstimate').decode().splitlines()
assert len(parent_leaves) == 357
changed = {'RicciFlowSharpEstimate/Geometry/AreaWarpCalibration.lean'}
check_blobs([p for p in parent_leaves if p not in changed], PARENT)
new = {'RicciFlowSharpEstimate/Geometry/' + p + '.lean' for p in
       ['AreaSlopeMass', 'AreaSlopeCalibration', 'RotationalStrictPinching']}
physical = {str(p.relative_to(ROOT)) for p in (ROOT / 'RicciFlowSharpEstimate').rglob('*.lean')}
assert physical == set(parent_leaves) | new and len(physical) == 360

phase1 = git('ls-tree', '-r', '--name-only', '721fd81',
             'RicciFlowSharpEstimate').decode().splitlines()
assert len(phase1) == 149
check_blobs(phase1, '721fd81')
baseline = json.loads((ROOT / '.references/phase2-unrestricted-20261012/preservation-receipt.json').read_text())
for p, h in baseline['preserved_phase1_loop_hashes'].items():
    assert sha(ROOT / p) == h, p
paper = {p: h for p, h in baseline['preserved_artifact_hashes'].items() if p.startswith('paper/')}
for p, h in paper.items():
    assert sha(ROOT / p) == h, p
assert sha(ROOT / '.references/TASK.md') == baseline['preserved_artifact_hashes']['.references/TASK.md']
assert sha(ROOT / '.references/phase2-unrestricted-20261012/TASK.md') == baseline['phase2_task_sha256']
evidence = git('ls-tree', '-r', '--name-only', PARENT, 'docs/evidence').decode().splitlines()
check_blobs(evidence, PARENT)

immutable = (ROOT / '.humanize/rlcr/2026-10-12_19-57-48/goal-tracker.md').read_bytes().split(b'## MUTABLE SECTION')[0]
immutable_hash = hashlib.sha256(immutable).hexdigest()
assert immutable_hash == '3222e336ce7edb57d5cd4794bbc6c0c43ec833a595d69254214c98a8e6ded6e1'
kb = sha(ROOT / '.humanize/bitlesson.md')
assert kb == '48215551a10642e35fca9e2bcbb8dfa5fba713b266a62d43c5721903e1e83855'
restart = Path('/home/ubuntu/.local/state/rfse-route-recovery-20261015')
historical = json.loads((restart / 'rounds-before.json').read_text())
mutable = {'.humanize/rlcr/2026-10-12_19-57-48/goal-tracker.md',
           '.humanize/rlcr/2026-10-12_19-57-48/tasks.json'}
historical = {p: h for p, h in historical.items() if p not in mutable}
for p, h in historical.items():
    assert sha(ROOT / p) == h, p

receipt = json.loads((OUT / 'receipt.json').read_text())
for p, h in receipt['source_hashes'].items():
    assert sha(ROOT / p) == h, p
assert len(receipt['source_hashes']) == 365
labels = []
for r in receipt['commands']:
    assert r['exit_code'] == 0
    raw = OUT / (r['label'] + '.txt')
    assert sha(raw) == r['output_sha256'], r['label']
    labels.append(r['label'])
assert len(labels) == len(set(labels)) == 366

consumer = json.loads((S / 'SlopeGapChecks.completion.json').read_text())
assert consumer['exit_code'] == 0
assert sha(S / 'SlopeGapChecks.lean') == consumer['source_sha256']
assert sha(S / 'SlopeGapChecks.txt') == consumer['output_sha256']
assert not (S / 'SlopeGapChecks.txt').read_bytes()
assert consumer['canonical_imports_without_scratch_overlay']

report = {
    'parent_revision': PARENT, 'phase1_status': 'COMPLETE; preserved',
    'phase2_status': 'OPEN', 'unchanged_parent_leaves': 356,
    'changed_parent_leaves': sorted(changed), 'new_canonical_modules': sorted(new),
    'current_canonical_modules': len(physical), 'new_public_theorems': 5,
    'unchanged_phase1_sources': len(phase1),
    'unchanged_phase1_workflow_files': len(baseline['preserved_phase1_loop_hashes']),
    'unchanged_prior_evidence_files': len(evidence),
    'unchanged_pre_restart_round_files': len(historical),
    'paper_sha256': paper, 'both_tasks_unchanged': True,
    'immutable_tracker_prefix_sha256': immutable_hash, 'bitlesson_sha256': kb,
    'pins_sha256': {p: sha(ROOT / p) for p in ['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']},
    'native_receipt_sha256': sha(OUT / 'receipt.json'),
    'current_native_inputs': len(receipt['source_hashes']),
    'current_successful_outputs': len(receipt['commands']),
    'source_elaboration_reuse': 354, 'fresh_source_elaborations': 6,
    'consumer': consumer, 'audit_source_sha256': sha(__file__),
}
(S / 'preservation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['unchanged_parent_leaves',
    'unchanged_phase1_sources', 'unchanged_prior_evidence_files',
    'current_native_inputs', 'current_successful_outputs']}))
