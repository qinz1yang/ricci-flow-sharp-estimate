from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/ubuntu/projects/rfse')
OUT = ROOT / 'docs/evidence/phase2-round-25-bellman-characteristics'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

cp = json.loads((OUT / 'checkpoint.json').read_text())
for p, h in {**cp['file_hashes'], **cp['document_hashes']}.items():
    assert sha(ROOT / p) == h, p
assert cp['mainline_progress_verdict'] == 'STALLED'
assert cp['new_canonical_modules'] == cp['new_canonical_declarations'] == 0
native = json.loads((OUT / 'research-native.json').read_text())
assert len(native['modules']) == len(native['diagnostics']) == 2
for r in native['modules']:
    name = Path(r['source_path']).name
    assert sha(OUT / name) == sha(r['source_path']) == r['source_sha256']
    assert sha(r['compiled_source_path']) == r['source_sha256']
    assert sha(Path(r['compiled_source_path']).with_suffix('.olean')) == r['olean_sha256']
    assert r['exit_code'] == 0
    log = OUT / name.replace('.lean', '.txt')
    assert sha(log) == r['output_sha256'] and not log.read_bytes()
    source = (OUT / name).read_text()
    assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|ofReduceBool)\b', source)
    assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth|synthInstance)', source)
for r in native['diagnostics']:
    assert r['exit_code'] == 0
    assert sha(OUT / Path(r['source_path']).name) == r['source_sha256']
    assert sha(OUT / Path(r['output_path']).name) == r['output_sha256']
assert not (OUT / 'ResearchLinters.txt').read_bytes()
raw = (OUT / 'ResearchAxioms.txt').read_text()
assert 'error:' not in raw and 'warning:' not in raw
assert len(re.findall(r'\bTYPE _private\.', raw)) == cp['private_research_declarations_selected']
prior_path = ROOT / cp['canonical_evidence']['receipt_path']
assert sha(prior_path) == cp['canonical_evidence']['receipt_sha256']
prior = json.loads(prior_path.read_text())
for p, h in prior['source_hashes'].items():
    assert sha(ROOT / p) == h, p
assert sha(ROOT / cp['canonical_evidence']['accepted_round24_checkpoint_path']) == cp['canonical_evidence']['accepted_round24_checkpoint_sha256']
advice = json.loads((OUT / 'advice-integration.json').read_text())
for name, h in advice['final_source_bindings'].items():
    assert sha(OUT / name) == h
assert sha(OUT / 'source-advice.md') == advice['report_sha256']
assert sha(OUT / 'source-advice.patch') == advice['patch_sha256']
assert subprocess.check_output(['git', 'branch', '--show-current'], cwd=ROOT, text=True).strip() == 'codex/rfse'
subprocess.run(['git', 'diff', '--check'], cwd=ROOT, check=True)
print(json.dumps({'checkpoint_sha256': sha(OUT / 'checkpoint.json'),
                  'research_files_bound': len(cp['file_hashes']), 'documents_bound': len(cp['document_hashes']),
                  'fresh_private_native_commands': len(native['modules']) + len(native['diagnostics']),
                  'selected_private_declarations': cp['private_research_declarations_selected'],
                  'reused_canonical_inputs': len(prior['source_hashes']),
                  'mainline_verdict': 'STALLED', 'new_canonical_declarations': 0,
                  'independent_outer_review': 'pending'}))
