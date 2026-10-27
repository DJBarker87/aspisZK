from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];rs=[]
for p in sorted(E.glob('XRx_L*/receipt.json')):
 r=json.loads(p.read_text());rs.append(r);a=r['attempt']
 for path,h in r['source_hashes'].items():
  snap=p.parent/'sources'/path
  if not snap.exists() or sha(snap)!=h:errors.append(a+': source snapshot mismatch '+path)
 if r.get('limits')!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+': limits')
 admission=json.loads((E/(a+'-reservation.json')).read_text())
 if admission.get('allowed') is not True:errors.append(a+': admission')
 if int(r['swaps'])!=0:errors.append(a+': swap')
 if len(r['source_revision'])!=40:errors.append(a+': source revision')
 if r['exit_status']==0:
  for ax in r['print_axioms']:
   if 'depends on axioms:' in ax:
    found=re.search(r'\[([^]]*)\]',ax)
    names=set(x.strip() for x in found.group(1).split(',') if x.strip())
    if names-{'propext','Classical.choice','Quot.sound'}:errors.append(a+': unexpected axioms '+ax)
 if not r['command'][0].endswith('/lake') or r['command'][1:3]!=['env','lean'] or '-M7000' not in r['command']:errors.append(a+': argv')
if [r['attempt'] for r in rs]!=[f'XRx_L{i:03d}' for i in range(1,101)]:errors.append('attempt set')
selected=json.loads((E/'XRx_accepted_selection.json').read_text())
for m,x in selected.items():
 p=E/(m+'.lean')
 if not p.exists() or sha(p) not in x['source_hashes'].values():errors.append(m+': final source differs from accepted receipt')
for c in json.loads((E/'XRx_reused_source_check.json').read_text()):
 if not c['equal']:errors.append(c['module']+': reused source mismatch')
def hashes(file):
 return {path:val for val,path in (line.split(None,1) for line in (E/file).read_text().splitlines())}
before=hashes('XRx_reused_cache_start.sha256');after=hashes('XRx_reused_cache_end.sha256')
for path,val in before.items():
 if after.get(path)!=val:errors.append('read-only reused object changed '+path)
head=sha(E/'XRx_top_before.lean.txt')
if head!=sha(E/'XRx_top_after.lean.txt') or head!='8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523':errors.append('headline statement mismatch')
changed=subprocess.check_output(['git','diff','--name-only','b2071654284ffd0da7486d083c8d9cc86e5a74b7'],text=True).splitlines()
for p in changed:
 if not p.startswith('evidence/extraction-assoc16-20261027/'):errors.append('outside scope '+p)
 for suffix in ['.olean','.ir','.elf','.so','.a','.o']:
  if p.endswith(suffix):errors.append('binary '+p)
result=dict(errors=errors,lean_launches=len(rs),passing=sum(r['exit_status']==0 for r in rs),failed=sum(r['exit_status']!=0 for r in rs),kani_runs=0,kani_budget=10,compiler_wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=sum(int(r['swaps']) for r in rs),accepted_new_modules=len(selected),accepted_new_theorems=sum(len(x['print_axioms']) for x in selected.values()),headline_sha256=head,persistent_cache_objects=len(hashes('XRx_cache_end.sha256')),read_only_start_objects=len(before),read_only_unchanged=True)
(E/'XRx_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'XRx_attempts.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rs))
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
