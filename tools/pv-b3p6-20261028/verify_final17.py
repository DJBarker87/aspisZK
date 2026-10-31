from pathlib import Path
import json,hashlib,re,subprocess
R=Path('evidence/pv-b3p6-20261028/resume17');inv=json.loads((R/'D537-final-host-inventory.json').read_text());bad=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,h in inv['hashes'].items():
 p=R/(name.removeprefix('resume17/'))
 if not p.exists()or sha(p)!=h:bad.append(name)
assert not bad,bad
assert '0 loaded units listed' in inv['scopes'],inv['scopes']
lean=[]
for i in list(range(73808,73828))+[73897]:
 p=R/f'lean-{i}';x=json.loads((p/'receipt/receipt.json').read_text());assert sha(p/'source.lean')==x['source_sha256']
 a=x['project_source_authority'];blob=subprocess.check_output(['git','cat-file','blob',a['blob']]);assert hashlib.sha256(blob).hexdigest()==a['sha256']==x['source_sha256']
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if x['exit_status']==0:assert x['print_axioms'] and all('sorryAx'not in z for z in x['print_axioms']),x
 lean.append({k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_sha256','lean_source_revision','print_axioms']})
ks=[]
for i in range(73945,73949):
 p=R/f'K{i}/receipt/receipt.json';x=json.loads(p.read_text());assert x['limits']['memory.swap.max']=='0'
 ks.append(dict(run=f'K{i}',**{k:x[k]for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']}))
t=json.loads((R/'TALLY-resume17.json').read_text());assert t['lean_attempts']==29 and t['next_unused_id']==73828
x=dict(target='V244 / runjoin op227 OPEN; target not yet established',verified_host_files=len(inv['hashes']),hash_mismatches=bad,live_scopes=[],lean=lean,kani=ks,combined_axioms_audit='73897 PASS, seven top declarations; standard axioms only',full_release_replay='NOT RUN; endpoint obligations remain. Focused direct-body import closure replay and axioms audit completed once at73897.',budget=dict(charged_lean=29,charged_extraction=20,charged_kani=18,charged_std=6,remaining_lean=11,remaining_extraction=10,remaining_kani=12,remaining_std=0),next=dict(lean=73828,extraction='N73927',kani='K73949',audits=[73898,73899]),retired_uncharged_ids=['K73944'],transport='SSH255 after73808 submission: recovered its existing failed receipt; never duplicated. No exact retry-interval measurement retained.',guards=dict(compile_wrapper_sha256=sha(Path('tools/pv-b3p6-20261028/compile_resume17.py')),failed_source_guard=True,refused_ids_retained=True),key_operations=[],release_source_edits=[],premise_changes=dict(removed=[],added=[],weakened=[]))
(R/'verification-summary-D537.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['verified_host_files','hash_mismatches','combined_axioms_audit','budget','next']}))
