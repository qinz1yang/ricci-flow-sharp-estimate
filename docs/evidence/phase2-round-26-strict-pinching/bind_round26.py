from pathlib import Path
import hashlib
import json
import shutil

R = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
O = R / 'docs/evidence/phase2-round-26-strict-pinching'
A = Path(json.loads((S / 'advice-path.json').read_text())['path'])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipt = json.loads((O / 'receipt.json').read_text())
assert len(receipt['source_hashes']) == 365 and len(receipt['commands']) == 366
for p, h in receipt['source_hashes'].items(): assert sha(R / p) == h, p
for c in receipt['commands']:
    assert c['exit_code'] == 0 and sha(O / (c['label'] + '.txt')) == c['output_sha256']
preservation = json.loads((S / 'preservation.json').read_text())
assert preservation['native_receipt_sha256'] == sha(O / 'receipt.json')
advice = json.loads((S / 'advice-integration.json').read_text())
for name, h in advice['final_source_bindings'].items():
    assert sha(R / 'RicciFlowSharpEstimate/Geometry' / name) == h, name
for name, row in advice['frozen_input_bindings'].items():
    assert sha(A / 'inputs' / name) == row['sha256'], name
assert sha(A / 'advice/report.md') == advice['report_sha256']
assert sha(A / 'advice/simplification.patch') == advice['patch_sha256']
worker = json.loads((S / 'worker-origin.json').read_text())
assert sha(worker['path']) == worker['sha256']

names = ['SlopeGapChecks.lean', 'SlopeGapChecks.txt', 'SlopeGapChecks.completion.json',
         'run_consumer.py', 'native_round26.py', 'finish_native_round26.py',
         'checker-before-signature-scope-fix.py', 'native-prefix-before-signature-repair.json',
         'signature-scope-development.txt', 'obsolete-signature-cancellation.json',
         'final-checker-policy-audit.json',
         'audit_round26.py', 'preservation.json', 'advice-integration.json',
         'worker-origin.json', 'attempts.md', 'bind_round26.py']
for name in names: shutil.copy2(S / name, O / name)
shutil.copy2(A / 'advice/report.md', O / 'source-advice.md')
patch_text = (A / 'advice/simplification.patch').read_text()
assert hashlib.sha256(patch_text.encode()).hexdigest() == advice['patch_sha256']
(O / 'source-advice-patch.json').write_text(json.dumps({
    'encoding': 'Exact original UTF-8 patch serialized as a JSON string',
    'original_patch_sha256': advice['patch_sha256'], 'patch': patch_text}, indent=2) + '\n')
files = {str(p.relative_to(R)): sha(p) for p in sorted(O.iterdir()) if p.name != 'checkpoint.json'}
docs = {p: sha(R / p) for p in ['docs/mathematical-status.md', 'docs/theorem-map.md',
                              'docs/research/phase2-unrestricted.md', 'docs/verification.md']}
sources = {p: sha(R / p) for p in ['RicciFlowSharpEstimate/Geometry/' + n + '.lean' for n in
    ['AreaWarpCalibration', 'AreaSlopeMass', 'AreaSlopeCalibration', 'RotationalStrictPinching']]}
cp = {
    'round': 26, 'parent_revision': '978eec876a9ed7ee815bd0d936d395a53a8ce91c',
    'phase1_status': 'COMPLETE; preserved', 'phase2_status': 'OPEN',
    'mainline_progress_verdict': 'ADVANCED',
    'mainline_result': 'The contracted independent alternative proves 1+sqrt(3/2) < C_rot through the complete slope-weighted calibration and genuine weak recovery; the sharp value is undetermined',
    'principal_attempt': 'At diagnostic cap5/2 the specified epsilon*f*r^2*v^2/(r^2+v^2) angular perturbation fails the actual quartic-profile midpoint sign test for every amplitude. This is a labeled research calculation, not a new canonical theorem, action negativity or a general angular no-go.',
    'positive_dependency_map': ['original physical state bounds and full calibration',
        'retained positive middle Bernstein blocks and genuine pole FTC',
        'smooth complete-action lower bound by actual slope-weighted mass',
        'each recovery box gives its own scale lower bound; no boxes are identified',
        'bounded primitive multipliers and strong L2 probe recovery preserve exact weighted mass',
        'same-object complete-action convergence gives independent weak comparison',
        'positive-curvature primitive has null slope-zero set; physical mass1 gives strict positivity',
        'accepted actual threshold zero object excludes the entire displayed cap range'],
    'new_canonical_modules': 3, 'changed_parent_modules': 1, 'new_public_theorems': 5,
    'new_public_definitions': 0, 'source_hashes': sources, 'document_hashes': docs,
    'native_receipt_path': str((O / 'receipt.json').relative_to(R)),
    'native_receipt_sha256': sha(O / 'receipt.json'),
    'native_inputs': 365, 'successful_native_outputs': 366,
    'canonical_modules': 360, 'reused_source_elaborations': 354,
    'fresh_source_elaborations': 6, 'canonical_consumer_sha256': sha(S / 'SlopeGapChecks.lean'),
    'consumer_canonical_imports_without_overlay': True,
    'consumer_retains_all_four_graph_limits_and_complete_action': True,
    'allowed_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'declaration_linters': ['unusedArguments', 'simpNF', 'synTaut'],
    'defLemma_replacement': 'Native getConstInfo/Meta.isProp declaration-kind inspection',
    'native_continuation': receipt['execution_orchestration'],
    'source_advice': advice,
    'portable_source_advice_patch': 'source-advice-patch.json; exact original bytes recover from its patch string',
    'worker_original': worker,
    'final_attempt_record_sha256': sha(S / 'attempts.md'),
    'frozen_advice_attempt_context_sha256': advice['frozen_input_bindings']['attempts.md']['sha256'],
    'remaining_original_gates': ['informative sharp construction and justified cap selection',
        'independent universal original scalar/all-form safety at that selected value',
        'compatible original zero object and same-object recovery, then derived minimality and cap expansion',
        'sharp identification, original smooth endpoint equality/attainment and all-form transfer',
        'every used state/chart/polar/interface/path/normalization/recovery bridge',
        'separate PhaseII manuscript and final native, independent mathematical/manuscript review and private delivery'],
    'independent_review': 'One configured outer delta review pending; advice and Root audits are not acceptance',
    'file_hashes': files,
    'no_local_authority_reference_workflow_bitlesson_or_accepted_paper_delivered': True,
}
(O / 'checkpoint.json').write_text(json.dumps(cp, indent=2) + '\n')
print(json.dumps({'checkpoint_sha256': sha(O / 'checkpoint.json'),
                  'evidence_files': len(files), 'source_bindings': len(sources),
                  'document_bindings': len(docs)}))
