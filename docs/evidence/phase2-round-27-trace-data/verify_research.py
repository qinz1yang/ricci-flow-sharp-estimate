from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path('/home/ubuntu/projects/rfse')
OUT=ROOT/'docs/evidence/phase2-round-27-trace-data'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
cp=json.loads((OUT/'checkpoint.json').read_text())
for p,h in {**cp['file_hashes'],**cp['document_hashes']}.items():assert sha(ROOT/p)==h,p
assert cp['mainline_progress_verdict']=='STALLED'
assert cp['new_canonical_modules']==cp['new_canonical_declarations']==0
native=json.loads((OUT/'research-native.json').read_text())
assert len(native['modules'])==1 and len(native['diagnostics'])==2
for r in native['modules']:
 name=Path(r['source_path']).name
 assert sha(OUT/name)==sha(r['source_path'])==sha(r['compiled_source_path'])==r['source_sha256']
 assert sha(Path(r['compiled_source_path']).with_suffix('.olean'))==r['olean_sha256']
 assert r['exit_code']==0
 log=OUT/name.replace('.lean','.txt')
 assert sha(log)==r['output_sha256'] and not log.read_bytes()
 source=(OUT/name).read_text()
 assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|ofReduceBool)\b',source)
 assert not re.search(r'set_option|nolint',source)
for r in native['diagnostics']:
 assert r['exit_code']==0
 assert sha(OUT/Path(r['source_path']).name)==r['source_sha256']
 assert sha(OUT/Path(r['output_path']).name)==r['output_sha256']
assert not (OUT/'ResearchLinters.txt').read_bytes()
raw=(OUT/'ResearchAxioms.txt').read_text()
assert 'error:' not in raw and 'warning:' not in raw
n=cp['private_research_declarations_selected']
assert len(re.findall(r'\bTYPE _private\.',raw))==n
for decl in re.findall(r'\bprivate\s+(?:theorem|def)\s+([A-Za-z_][A-Za-z0-9_]*)',(OUT/'FreeTraceChecks.lean').read_text()):
 assert re.search(r'TYPE _private\.FreeTraceChecks\.[^\n]*\.'+decl+r':',raw),decl
prior_path=ROOT/cp['canonical_evidence']['receipt_path']
assert sha(prior_path)==cp['canonical_evidence']['receipt_sha256']
prior=json.loads(prior_path.read_text())
for p,h in prior['source_hashes'].items():assert sha(ROOT/p)==h,p
for r in prior['commands']:
 assert r['exit_code']==0
 assert sha(prior_path.parent/(r['label']+'.txt'))==r['output_sha256']
advice=json.loads((OUT/'advice-integration.json').read_text())
assert sha(OUT/'FreeTraceChecks.lean')==advice['final_Root_source_sha256']
assert sha(OUT/'source-advice.md')==advice['report_sha256']
assert sha(OUT/'source-advice.patch')==advice['patch_sha256']
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='codex/rfse'
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
print(json.dumps({'checkpoint_sha256':sha(OUT/'checkpoint.json'),'research_files_bound':len(cp['file_hashes']),
 'documents_bound':len(cp['document_hashes']),'fresh_private_native_commands':3,
 'selected_private_declarations':n,'reused_canonical_inputs':len(prior['source_hashes']),
 'reused_canonical_outputs':len(prior['commands']),'mainline_verdict':'STALLED',
 'new_canonical_declarations':0,'independent_outer_review':'pending'}))
