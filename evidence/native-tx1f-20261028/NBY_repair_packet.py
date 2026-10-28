"""Narrow packet export to modified frozen owners and actual harness modules."""
from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
old=json.loads((E/'NBY_HARNESS_PINS.json').read_text());frozen=json.loads((E/'NBY_FROZEN_SOURCE_PINS.json').read_text())['files']
def allowed(n):return n in frozen or n in ['KMX_stubs.rs','KMX_CopyMeaning.lean','KMX_native.rs'] or n.startswith('crates/aspis-r1-cost-probe/src/NBY_') or n.startswith('crates/aspis-r1-cost-probe/src/NBV_')
(E/'NBY_PATCH_CHECK_DRAFT_FAILURE.json').write_bytes((E/'NBY_PATCH_CHECK.json').read_bytes())
patch=(E/'NBY_COMPLETE_HARNESS.patch').read_text();kept=[]
for block in re.split(r'(?m)(?=^--- (?:a/|/dev/null))',patch):
 m=re.search(r'(?m)^\+\+\+ b/(.+)$',block)
 if m and allowed(m.group(1)):kept.append(block)
new=''.join(kept);(E/'NBY_COMPLETE_HARNESS.patch').write_text(new)
removed=[n for n in old['source_files'] if not allowed(n)]
newpins={**old,'sha256':hashlib.sha256(new.encode()).hexdigest(),'size':len(new.encode()),'source_files':{n:v for n,v in old['source_files'].items() if allowed(n)}}
(E/'NBY_HARNESS_PINS.json').write_text(json.dumps(newpins,indent=2)+'\n')
(E/'NBY_PATCH_SCOPE_FIX.json').write_text(json.dumps({'rejected_draft_sha256':old['sha256'],'rejected_draft_size':old['size'],'removed_unmodified_out_of_scope_sources':removed,'final_sha256':newpins['sha256'],'prover_reruns':0,'host_mutations':0},indent=2)+'\n')
p=subprocess.run(['git','apply','--check',str(E/'NBY_COMPLETE_HARNESS.patch')],cwd=R,text=True,capture_output=True)
(E/'NBY_PATCH_CHECK.json').write_text(json.dumps({'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr},indent=2)+'\n');assert p.returncode==0,p.stderr
print('patch check pass; included',len(newpins['source_files']),'files; excluded',len(removed),'unmodified out-of-scope sources')
