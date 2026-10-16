from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path('/home/ubuntu/projects/rfse')
S = Path(__file__).parent
OUT = ROOT / 'docs/evidence/phase2-round-25-bellman-characteristics'
A = Path(json.loads((S / 'advice-path.json').read_text())['path'])

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

n = json.loads((S / 'research-native.json').read_text())
assert len(n['modules']) == 2 and len(n['diagnostics']) == 2
for r in n['modules']:
    assert r['exit_code'] == 0
    assert sha(r['source_path']) == sha(r['compiled_source_path']) == r['source_sha256']
    assert sha(Path(r['compiled_source_path']).with_suffix('.olean')) == r['olean_sha256']
    assert not (S / (r['name'] + '.txt')).read_bytes()
for r in n['diagnostics']:
    assert r['exit_code'] == 0 and sha(r['source_path']) == r['source_sha256']
    assert sha(r['output_path']) == r['output_sha256']
assert not (S / 'ResearchLinters.txt').read_bytes()
raw = (S / 'ResearchAxioms.txt').read_text()
count = int(re.search(r'Selected (\d+) research declarations', raw).group(1))
assert len(re.findall(r'\bTYPE _private\.', raw)) == count
for name in ['QuadraticFluxProbe', 'FreeCharacteristicProbe']:
    source = (S / (name + '.lean')).read_text()
    for decl in re.findall(r'\bprivate\s+(?:theorem|def)\s+([A-Za-z_][A-Za-z0-9_]*)', source):
        assert re.search(r'TYPE _private\.' + name + r'\.[^\n]*\.' + decl + r':', raw), decl
advice = json.loads((S / 'advice-integration.json').read_text())
assert advice['final_root_sources_match_declared_literal_transformations']
for name, h in advice['final_source_bindings'].items():
    assert sha(S / name) == h
manifest = json.loads((A / 'inputs.json').read_text())
for name, r in manifest.items():
    assert sha(A / 'inputs' / name) == r['sha256']
assert sha(A / 'advice/report.md') == advice['report_sha256']
assert sha(A / 'advice/simplification.patch') == advice['patch_sha256']

names = ['QuadraticFluxProbe.lean', 'FreeCharacteristicProbe.lean',
         'QuadraticFluxProbe.txt', 'FreeCharacteristicProbe.txt',
         'ResearchLinters.lean', 'ResearchAxioms.lean', 'ResearchLinters.txt', 'ResearchAxioms.txt',
         'research-native.json', 'current-environment.json', 'preservation.json',
         'advice-integration.json', 'worker-origin.json', 'run_module.py', 'run_diagnostics.py',
         'audit_unchanged.py', 'bind_research.py', 'verify_research.py']
OUT.mkdir(exist_ok=True)
for name in names:
    shutil.copyfile(S / name, OUT / name)
shutil.copyfile(A / 'advice/report.md', OUT / 'source-advice.md')
shutil.copyfile(A / 'advice/simplification.patch', OUT / 'source-advice.patch')
files = {str(p.relative_to(ROOT)): sha(p) for p in sorted(OUT.iterdir()) if p.name != 'checkpoint.json'}
docs = {p: sha(ROOT / p) for p in ['docs/mathematical-status.md', 'docs/theorem-map.md',
                                  'docs/research/phase2-unrestricted.md', 'docs/verification.md']}
cp = {
    'round': 25, 'parent_revision': 'aaa93b605193446abfa4ed25a74db0e0086bd5b4',
    'phase1_status': 'COMPLETE; preserved', 'phase2_status': 'OPEN',
    'mainline_progress_verdict': 'STALLED',
    'mainline_result': 'Sharp producer not delivered; specified whole-state tight quadratic Bellman producer has a native selected-box incompatibility theorem',
    'new_canonical_modules': 0, 'new_canonical_declarations': 0,
    'safe_lower_bound_unchanged': '1+sqrt(3/2) <= C_rot; no new safe cap or identification',
    'fresh_native_scope': 'Two private sources including the full actual flux and selected-box minimum consumer, declaration kinds/linters, explicit types and actual transitive axioms',
    'private_research_declarations_selected': count,
    'all_named_private_source_declarations_covered': True,
    'allowed_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'declaration_linters': ['unusedArguments', 'simpNF', 'synTaut'],
    'defLemma_replacement': 'Native declaration-kind inspection via getConstInfo and Meta.isProp',
    'private_import_overlay': 'Root-only unchanged canonical artifacts and isolated private compiled outputs; no worker cache or canonical source mutation',
    'negative_scope': [
        'One box witness selected from each actual zero recoverable global minimum at C>1 with continuous interior r,p; no arbitrary-box theorem is advertised',
        'Whole-state tightness and nonnegative remainder for all controls/directions on an open geometry-state enclosure are extra hypotheses of this producer',
        'The stated coefficient regularity and explicit a.e. remainder saturation are retained; saturation is not derived from zero action',
        'The actual state is (x,warp K x,warpSlope K x), v=warp K x*p x, with the same original K,r,p,z and selected curvature box',
        'No claim that every ambient state is physically reachable, that every comparison is tight, or that slack/restricted-domain/nonsmooth/nonquadratic certificates are impossible',
        'No new global positive comparison, determining value, sharp zero producer or original smooth endpoint theorem',
    ],
    'canonical_evidence': {
        'action': 'reuse unchanged accepted Round23 canonical gate and Round24 restricted checkpoint review/evidence',
        'receipt_path': 'docs/evidence/phase2-round-23-warp-calibration/receipt.json',
        'receipt_sha256': '6a454dfdb414a69f0fd0aebf75256618c9ad1e0caac979cedb633ad91561afd3',
        'unchanged_inputs': 362, 'unchanged_successful_outputs': 363,
        'unchanged_modules': 357, 'fresh_root_build_or_full_suite_query': False,
        'accepted_round24_checkpoint_path': 'docs/evidence/phase2-round-24-field-feasibility/checkpoint.json',
        'accepted_round24_checkpoint_sha256': 'abca92fea074489d728cea7cf66fc97747233e7fee5c6be159ad8ca544f52176',
    },
    'source_advice': advice,
    'worker_packet': json.loads((S / 'worker-origin.json').read_text()),
    'attempt_record': {'path': str(S / 'attempts.md'), 'sha256': sha(S / 'attempts.md')},
    'next_action': 'Rotate the specified tight producer; actually test global angular/slack characteristic production, including nodal and zero states, with an original zero object and informative selection',
    'remaining_original_gates': ['informative determination and justified selection',
        'independent original all-form safety at the characterized sharp value',
        'tied original zero object and every used domain, polar, interface, chart, path and recovery bridge',
        'sharp original smooth witnesses, exact original smooth endpoint and all-form equality transfer',
        'separate PhaseII manuscript, native, independent mathematical/manuscript review and private delivery'],
    'independent_review': 'One configured Astra/max outer delta review pending; no second acceptance reviewer launched',
    'file_hashes': files, 'document_hashes': docs,
    'no_local_authority_reference_workflow_or_accepted_paper_delivered': True,
}
(OUT / 'checkpoint.json').write_text(json.dumps(cp, indent=2) + '\n')
print(json.dumps({'selected_private_declarations': count, 'research_files': len(files),
                  'checkpoint_sha256': sha(OUT / 'checkpoint.json'), 'mainline': 'STALLED'}))
