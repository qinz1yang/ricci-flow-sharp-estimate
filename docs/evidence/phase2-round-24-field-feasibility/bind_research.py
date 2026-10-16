from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
OUT = ROOT / 'docs/evidence/phase2-round-24-field-feasibility'
ADVICE = Path('/tmp/hmz-fence-rfse-route-_1tj3d8t/math-target-round24-advice-7n1_4eey')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

native = json.loads((S / 'research-native.json').read_text())
assert all(r['exit_code'] == 0 for r in native['modules'] + native['diagnostics'])
assert (S / 'ResearchLinters.txt').read_bytes() == b''
axioms = (S / 'ResearchAxioms.txt').read_text()
match = re.search(r'Selected (\d+) research declarations', axioms)
assert match and int(match.group(1)) >= 30
count = int(match.group(1))
assert len(re.findall(r'\bTYPE _private\.', axioms)) == count
for suffix in ['.negative_actual_density', '.trial_density_scale', '.no_constant_history_enclosure',
               '.calibration_det_pos_on_rectangle', '.history_defect_value']:
    assert suffix in axioms, suffix
for r in native['modules']:
    assert sha(r['source_path']) == r['source_sha256']
    assert sha(r['compiled_source_path']) == r['source_sha256']
for r in native['diagnostics']:
    assert sha(r['source_path']) == r['source_sha256']
    assert sha(r['output_path']) == r['output_sha256']
advice = json.loads((ADVICE / 'inputs.json').read_text())
for name, r in advice.items():
    assert sha(ADVICE / 'inputs' / name) == r['sha256']
    assert sha(r['source_path']) == r['sha256']
assert not ((ADVICE / 'advice/report.md').stat().st_mode & 0o222)

OUT.mkdir(exist_ok=True)
names = ['AffineFieldChecks.lean', 'WarpOnlyPencilChecks.lean', 'HistoryStateChecks.lean',
         'AffineFieldChecks.txt', 'WarpOnlyPencilChecks.txt', 'HistoryStateChecks.txt',
         'ResearchLinters.lean', 'ResearchAxioms.lean', 'ResearchLinters.txt', 'ResearchAxioms.txt',
         'research-native.json', 'current-environment.json', 'preservation.json',
         'run_module.py', 'run_diagnostics.py', 'audit_unchanged.py', 'bind_research.py',
         'verify_research.py']
for name in names:
    shutil.copyfile(S / name, OUT / name)
shutil.copyfile(ADVICE / 'advice/report.md', OUT / 'source-advice.md')
files = {str(p.relative_to(ROOT)): sha(p) for p in sorted(OUT.iterdir())
         if p.name != 'checkpoint.json'}
docs = {p: sha(ROOT / p) for p in ['docs/mathematical-status.md', 'docs/theorem-map.md',
                                  'docs/research/phase2-unrestricted.md', 'docs/verification.md']}
worker = Path('/tmp/hmz-fence-rfse-route-_1tj3d8t/math-target-round24-history-1co0bh6j')
checkpoint = {
    'round': 24, 'parent_revision': '088b48f5ede5e1f072e3d00540b616b28c6e4bc4',
    'phase1_status': 'COMPLETE; preserved', 'phase2_status': 'OPEN',
    'mainline_progress_verdict': 'STALLED',
    'mainline_result': 'Joint sharp field/zero-object producer not delivered; restricted research diagnostics only',
    'new_canonical_modules': 0, 'new_canonical_declarations': 0,
    'safe_lower_bound_unchanged': '1+sqrt(3/2) <= C_rot; no identification or new bound',
    'fresh_native_scope': 'Three isolated private research probes, exact declared types, declaration kinds/linters and actual axiom closures only',
    'private_research_declarations_selected': count,
    'anonymous_examples': 'Fixture examples are kernel-checked during source elaboration; they are not exported declarations and no standalone signature-query row is claimed for them',
    'allowed_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'declaration_linters': ['unusedArguments', 'simpNF', 'synTaut'],
    'defLemma_replacement': 'Native getConstInfo and Meta.isProp declaration-kind inspection',
    'private_import_overlay': 'Root-only unchanged canonical artifacts plus isolated compiled probes; no canonical source or checker change',
    'canonical_evidence': {
        'action': 'reuse unchanged accepted Round23 source/root/signature/linter/axiom evidence',
        'receipt_path': 'docs/evidence/phase2-round-23-warp-calibration/receipt.json',
        'receipt_sha256': '6a454dfdb414a69f0fd0aebf75256618c9ad1e0caac979cedb633ad91561afd3',
        'unchanged_inputs': 362, 'unchanged_successful_outputs': 363,
        'unchanged_modules': 357, 'fresh_root_build_or_full_suite_query': False,
    },
    'scope_limits': [
        'Negative candidate density at an actual normalized smooth fixture is pointwise, not negative original action or cap unsafety',
        'Warp-only rigidity retains the nonnegative open-rectangle premise, f>0 and a>0; original reachability and weak equality bridges are not supplied',
        'Constant-history incompatibility rejects the stated enclosure conditions at diagnostic cap5/2; enclosure-boundary physical realization is not proved',
        'The separate original upper-contact history state is no sharp zero object or global comparison',
        'No new independent global safety, determining value/selection, original smooth endpoint or all-form equality theorem',
    ],
    'route_status': 'Low-order warp/constant-history construction parked UNRESOLVED/UNREFUTED at full original scope after two substantive unsuccessful tests',
    'next_action': 'Choose a substantively different full-state/characteristic producer; retain genuine history derivatives, global Q sign and the tied original zero object together',
    'remaining_original_gates': ['informative determination and justified selection',
        'independent original all-form safety at the characterized sharp value',
        'every used domain/polar/interface/path/normalization/Haar/recovery bridge',
        'sharp original smooth witnesses and endpoint equality/attainment with all-form transfer',
        'separate PhaseII manuscript, native, single independent outer review and private delivery'],
    'source_advice': {'path': str(ADVICE / 'advice/report.md'),
                      'report_sha256': sha(ADVICE / 'advice/report.md'),
                      'manifest_sha256': sha(ADVICE / 'inputs.json'),
                      'matching_frozen_source_bindings': 6,
                      'recommendation': 'NO CHANGE; source-only advice, not acceptance',
                      'lease_released': True},
    'worker_packets': [{
        'path': str(p), 'sha256': sha(p),
        'status': 'PROVISIONAL source-only candidate; Root final native sources/outputs are separately bound',
    } for p in [worker / 'HistoryStateProbe.lean', worker / 'pencil/AffinePencilProbe.lean']],
    'attempt_record': {'path': str(S / 'attempts.md'), 'sha256': sha(S / 'attempts.md')},
    'independent_review': 'One configured Astra/max outer delta review pending; no additional acceptance reviewer launched',
    'file_hashes': files, 'document_hashes': docs,
    'no_local_authority_reference_workflow_or_accepted_paper_delivered': True,
}
(OUT / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
print(json.dumps({'selected_private_declarations': count, 'research_files': len(files),
                  'checkpoint_sha256': sha(OUT / 'checkpoint.json'), 'mainline': 'STALLED'}))
