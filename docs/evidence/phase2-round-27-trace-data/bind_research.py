from pathlib import Path
import hashlib,json,re,shutil
ROOT=Path('/home/ubuntu/projects/rfse')
S=Path(__file__).parent
OUT=ROOT/'docs/evidence/phase2-round-27-trace-data'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
n=json.loads((S/'research-native.json').read_text())
assert len(n['modules'])==1 and len(n['diagnostics'])==2
for r in n['modules']:
 assert r['exit_code']==0
 assert sha(r['source_path'])==sha(r['compiled_source_path'])==r['source_sha256']
 assert sha(Path(r['compiled_source_path']).with_suffix('.olean'))==r['olean_sha256']
 assert not (S/(r['name']+'.txt')).read_bytes()
for r in n['diagnostics']:
 assert r['exit_code']==0 and sha(r['source_path'])==r['source_sha256']
 assert sha(r['output_path'])==r['output_sha256']
assert not (S/'ResearchLinters.txt').read_bytes()
raw=(S/'ResearchAxioms.txt').read_text()
count=int(re.search(r'Selected (\d+) research declarations',raw).group(1))
assert len(re.findall(r'\bTYPE _private\.',raw))==count
source=(S/'FreeTraceChecks.lean').read_text()
source_names=re.findall(r'\bprivate\s+(?:theorem|def)\s+([A-Za-z_][A-Za-z0-9_]*)',source)
for name in source_names:assert re.search(r'TYPE _private\.FreeTraceChecks\.[^\n]*\.'+name+r':',raw),name
advice=json.loads((S/'advice-integration.json').read_text())
A=Path(json.loads((S/'advice-path.json').read_text())['path'])
for name,r in json.loads((A/'inputs.json').read_text()).items():assert sha(A/'inputs'/name)==r['sha256']
assert sha(A/'advice/report.md')==advice['report_sha256']
assert sha(A/'advice/simplification.patch')==advice['patch_sha256']
assert sha(S/'FreeTraceChecks.lean')==advice['final_Root_source_sha256']
explore=json.loads((S/'exploratory-command.json').read_text())
for name,h in explore['source_hashes'].items():assert sha(S/name)==h,name
for r in explore['commands']:assert r['exit_code']==0
names=['FreeTraceChecks.lean','FreeTraceChecks.txt','ResearchLinters.lean','ResearchAxioms.lean',
 'ResearchLinters.txt','ResearchAxioms.txt','research-native.json','current-environment.json',
 'preservation.json','worker-origin.json','advice-integration.json','run_module.py',
 'run_diagnostics.py','audit_unchanged.py','bind_research.py','verify_research.py',
 'attempts.md','attempt-status.json','trace-input-bindings.json','Root-proof-repairs.json','ck_angular_test.py','actual_state_test.py',
 'actual-state-output.txt','polynomial_test.py','polynomial_driver.py',
 'polynomial-output.txt','polynomial-results.json','exploratory-command.json']
OUT.mkdir(exist_ok=True)
for name in names:shutil.copyfile(S/name,OUT/name)
shutil.copyfile(A/'advice/report.md',OUT/'source-advice.md')
shutil.copyfile(A/'advice/simplification.patch',OUT/'source-advice.patch')
file_hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(OUT.iterdir()) if p.name!='checkpoint.json'}
documents={p:sha(ROOT/p) for p in ['docs/mathematical-status.md','docs/theorem-map.md',
 'docs/research/phase2-unrestricted.md','docs/verification.md']}
cp={'round':27,'parent_revision':'62e08abf33c2dc3d9ba808c129648a46f3081ac0',
 'phase1_status':'COMPLETE; preserved','phase2_status':'OPEN','mainline_progress_verdict':'STALLED',
 'mainline_result':'CK trace and positive-axis/polar-joined extension did not produce complete global sign or a compatible original zero object; one polynomial alternative did not improve the accepted upper information',
 'new_canonical_modules':0,'new_canonical_declarations':0,
 'accepted_bounds_unchanged':'1+sqrt(3/2)<C_rot<C_CK; neither sharp value nor endpoint determined',
 'fresh_native_scope':'One private source with actual potential partials, full density completion, exact free-axis square and negative H for each epsilon at the actual round probe jet; kinds/linters, exact types and actual transitive axioms',
 'private_named_source_declarations':len(source_names),'private_research_declarations_selected':count,
 'all_named_private_source_declarations_covered':True,
 'allowed_transitive_axioms':['propext','Classical.choice','Quot.sound'],
 'declaration_linters':['unusedArguments','simpNF','synTaut'],
 'defLemma_replacement':'Native declaration-kind inspection via getConstInfo and Meta.isProp',
 'private_import_overlay':'Root-only unchanged canonical source/artifact links and isolated private outputs; no worker cache or canonical mutation',
 'negative_scope':['Only the explicitly stated CK free-trace rational-angular family is rejected for every amplitude by the native diagnostic.',
  'Actual K=2,x=1/4 has f=3/8,b=1 and the literal polynomial probe has r=1 and v=t; the potential partials are proved rather than supplied.',
  'The full six-entry density and all curvature/lower-order terms are retained. Negative pointwise H is not negative integrated action or round-cap unsafety.',
  'Joined characteristic/polar formulas, positive axis slack and all subsequent mixed-sign tests remain separately labeled research calculations; no native global/polar/weak-extension theorem is credited.',
  'Finite polynomial blocks and floating sign-change roots are exploratory; no full-family positivity, root uniqueness, improved original upper witness or cap determination is asserted.',
  'No general angular impossibility, original sharp zero producer, global comparison or original smooth endpoint theorem.'],
 'canonical_evidence':{'action':'Reuse unchanged accepted Round26 canonical gate and outer delta review; no fresh canonical build or old private-proof replay',
  'receipt_path':'docs/evidence/phase2-round-26-strict-pinching/receipt.json',
  'receipt_sha256':'0db3f375f387a538709b078e4e7417e3bed98c3f0fe017fa28989de1479c3d26',
  'unchanged_inputs':365,'unchanged_successful_outputs':366,'unchanged_modules':360,
  'fresh_root_build_or_full_suite_query':False},
 'source_advice_scope':'NO CHANGE on the frozen provisional worker original only; final Root native proof repairs separately recorded and source-bound, not attributed to advice or independent acceptance',
 'source_advice':advice,'worker_packet':json.loads((S/'worker-origin.json').read_text()),
 'preservation':json.loads((S/'preservation.json').read_text()),
 'attempt_record':{'path':'docs/evidence/phase2-round-27-trace-data/attempts.md','sha256':sha(S/'attempts.md')},
 'next_action':'Park the tested angular trace mechanism after the Round26–27 unsuccessful attempts; select a substantively different nonlocal full-action comparison target, retaining every original positive dependency and final gate',
 'remaining_original_gates':['informative determining data and justified cap selection',
  'independent original scalar/all-form safety at the characterized sharp value',
  'tied original zero object with genuine derivative/domain/moment/box/mass and same-object recovery laws',
  'derived global minimality, accepted cap expansion and sharp original smooth witnesses at the selected value',
  'original smooth endpoint equality/attainment or nonattainment and same-metric all-form equality transfer',
  'every used state-domain, angular/chart, zero-state, polar, interface, admissible-path and recovery bridge',
  'separate PhaseII manuscript, final native/declaration/axiom gates, independent mathematical/manuscript review and private delivery'],
 'independent_review':'One configured outer delta review pending; no extra acceptance reviewer launched',
 'file_hashes':file_hashes,'document_hashes':documents,
 'no_local_authority_reference_workflow_bitlesson_or_accepted_paper_delivered':True}
(OUT/'checkpoint.json').write_text(json.dumps(cp,indent=2)+'\n')
print(json.dumps({'selected_private_declarations':count,'named_private_source_declarations':len(source_names),
 'research_files':len(file_hashes),'checkpoint_sha256':sha(OUT/'checkpoint.json'),'mainline':'STALLED'}))
