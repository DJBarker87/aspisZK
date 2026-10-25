#!/usr/bin/env python3
"""One focused read-only packet audit; no remote calls or build/proof execution."""
import json,hashlib,subprocess,time,resource
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'evidence/sbf-identity-20261024';T=R/'tools/sbf-identity-20261024';t=time.monotonic();checks=[];deps={}
def check(label,condition):
 checks.append(dict(check=label,passed=bool(condition)))
 if not condition:raise AssertionError(label)
def load(n):return json.loads((E/n).read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for folder in [E,T]:
 for p in sorted(folder.iterdir()):
  if p.name=='audit.json':continue
  b=p.read_bytes();check('bounded text '+str(p.relative_to(R)),len(b)<=5000000 and b'\0' not in b)
  deps[str(p.relative_to(R))]=dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
for name in ['current-global','current-content','current-source-tree','current-drivers']:
 x=load(name+'.json');r=load(name+'.receipt.json')
 check(name+' exact transport digest',r['stdout_sha256']==sha(E/(name+'.json')) and r['stdout_bytes']==(E/(name+'.json')).stat().st_size)
 check(name+' success and no swaps',r['exit']==0 and r['swaps']==0 and x['receipt']['exit']==0 and x['receipt']['swaps']==0)
 check(name+' source script digest',sha(R/r['script'])==r['script_sha256'])
 check(name+' no private symlink targets',not x['blocked_lookups'])
 check(name+' not historical',x['historical_identity'] is False)
 check(name+' bounded host RSS',x['receipt']['peak_rss_kib']<8*1024**2)
 for q in x.get('queries',[]):check(name+' metadata query '+str(q['command']),q['exit']==0)
content=load('current-content.json');global_=load('current-global.json');drivers=load('current-drivers.json');tree=load('current-source-tree.json');official=load('official-source-comparison.json');complete=load('complete-source-comparison.json');imm=load('immutable-assessment.json');plan=load('recapture-plan.json')
for p,row in global_['pins'].items():
 if p in content['pins']:check('stable overlapping current pin '+p,row['sha256']==content['pins'][p]['sha256'] and row['bytes']==content['pins'][p]['bytes'])
root=content['root']+'/platform-tools/rust/lib/rustlib/src/rust/'
for f in tree['files']:
 row=content['pins'][root+f['path']]
 check('stable source capture '+f['path'],row['sha256']==f['sha256'] and row['bytes']==f['bytes'] and row['mode']==f['mode'])
for row in official['comparisons']:
 p=E/('official-'+row['path'].replace('/','_')+'.txt')
 check('complete raw official sha256 '+row['path'],sha(p)==row['official_sha256']==row['current_sha256'] and row['match'])
for k in ['library/core/','library/alloc/']:
 x=complete['summary'][k];check('complete set/blob/mode '+k,not any(x[v] for v in ['mismatches','mode_mismatches','missing','extra']) and x['current_files']==x['official_files'])
for n in ['rust-top-tree.json','rust-library-tree.json','rust-src-tree.json']:
 x=load(n);payload=b''.join((row['mode'].lstrip('0')+' '+row['path']).encode()+b'\0'+bytes.fromhex(row['sha']) for row in x['tree'] if '/' not in row['path'])
 check('official Git tree object '+n,hashlib.sha1(b'tree '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==x['sha'])
check('official declared LLVM submodule',official['llvm_submodule'][0]['sha']=='78496716176191b2dfb728e5e38501812e7467db')
check('official tag resolved',load('platform-tag.txt')['object']['sha']=='e3ebfccfe63ba936dd6951ede390496c6bc2f296')
archive=next(a for a in load('platform-release.txt')['assets'] if a['name']=='platform-tools-linux-x86_64.tar.bz2')
check('official archive checksum metadata only',archive['digest']=='sha256:8b3861e93daf085ec12b65c4fac374d9bec4587a3de16871da6b08ab0c1d907e' and archive['size']==519270959)
for p,row in imm['inputs'].items():
 b=subprocess.check_output(['git','show',imm['base']+':'+p],cwd=R)
 check('immutable input '+p,hashlib.sha256(b).hexdigest()==row['sha256'] and len(b)==row['bytes'])
check('frozen source and full manifest',plan['source_revision']==imm['source_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387' and plan['source_input_count']==imm['source_input_count']==7978)
remote=next(iter(tree['pins'].values()));check('released source manifest agrees',remote['sha256']==imm['source_input_manifest']['sha256'] and remote['bytes']==imm['source_input_manifest']['bytes'])
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
for b in plan['builds']:
 m=b['mode'];check('planned ELF '+m,b['expected_sha256']==pins[m] and b['expected_sha256']==imm['modes'][m]['artifact-comparison']['sha256'])
 check('independent planned scope '+m,all(v in b['scope_command'] for v in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']) and b['cwd']==plan['stage']+'/src')
 check('offline locked tools unchanged '+m,all(v in b['command'] for v in ['--offline','--locked','--skip-tools-install']) and b['command'][b['command'].index('-j')+1]=='4')
 check('warm predecessor success noSwap '+m,b['historical_predecessor']['exit_status']==0 and b['historical_predecessor']['swaps']==0)
for doc in ['recapture-plan.json','complete-source-comparison.json']:
 for n,row in load(doc)['dependencies'].items():check(doc+' dependency '+n,sha(E/n)==row['sha256'])
for record in [load('plan-generation-receipt.json'),complete['receipt'],official['receipt'],imm['receipt'],load('official-fetch-receipt.json')]:
 cmd=record['command'];script=R/cmd[1];check('generation/fetch script '+cmd[1],sha(script)==record['script_sha256'])
check('before-after P7 unchanged','BoundaryStatements.P7 : Prop' in (E/'REPORT.md').read_text() and 'BoundaryEvidence.h_P7 : s.P7' in (E/'REPORT.md').read_text())
paths=subprocess.check_output(['git','diff','--name-only','3e9998bbfc','HEAD'],cwd=R,text=True).splitlines()
check('committed scope',all(p.startswith(('tools/sbf-identity-20261024/','evidence/sbf-identity-20261024/')) for p in paths))
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
r=dict(schema='sbf-identity-focused-audit-v1',claim='Offline integrity of current metadata, exact complete-source hash/mode comparison, retained historical input provenance and proposed plan. No historical identity/build/native/security conclusion.',checks=checks,check_count=len(checks),dependencies=deps,budgets=dict(compiler_build=0,lean=0,kani=0,extraction=0,rust_arithmetic=0,elf_gate=0,full_manifest=0),receipt=dict(command=['python3','tools/sbf-identity-20261024/audit-packet.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),script_sha256=sha(Path(__file__)),exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,print_axioms='N/A: no theorem, Lean import, compiler or ELF gate'))
(E/'audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(checks=len(checks),receipt=r['receipt']),indent=2))
