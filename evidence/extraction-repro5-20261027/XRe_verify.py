from pathlib import Path
import hashlib,json,re
B=Path(__file__).resolve().parent
rows=[];errors=[]
for p in sorted(B.glob('XRe_*/receipt.json')):
 r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 for key,value in r['source_hashes'].items():
  q=p.parent/'sources'/key
  if hashlib.sha256(q.read_bytes()).hexdigest()!=value:errors.append(str(q))
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(str(p)+':limits')
 if r['swaps']!='0':errors.append(str(p)+':swap')
 outcome='pass' if r['exit_status']==0 else 'timeout' if 'CBMC timed out' in log else 'unwinding' if 'unwinding failures' in log else 'failed'
 if r['kind']=='kani' and r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' not in log:errors.append(str(p)+':missing-success')
 rows.append(dict(attempt=r['attempt'],kind=r['kind'],source_revision=r['source_revision'],target=r['command'],source_hashes=r['source_hashes'],deps_fingerprint=r['deps_fingerprint'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),cgroup_peak_bytes=int(r['cgroup_memory_peak_bytes']),swaps=int(r['swaps']),axioms=r['print_axioms'],outcome=outcome))
kani=[r for r in rows if r['kind']=='kani'];lean=[r for r in rows if r['kind']=='lean'];translation=[r for r in rows if r['kind'] not in ['kani','lean']]
assert len(kani)==20 and len(lean)==2 and len(translation)==4,(len(kani),len(lean),len(translation))
assert [r['attempt'] for r in kani]==[f'XRe_K{i:03}' for i in range(1,21)]
assert json.loads((B/'XRe_HostAudit.json').read_text())['changed_source_files']==[]
assert (B/'XRe_Top.BEFORE.lean.txt').read_bytes()==(B/'XRe_Top.AFTER.lean.txt').read_bytes()
assert (B/'XRe_L002/sources/XRe_Reference.lean').read_bytes()==(B/'XRe_Reference.lean').read_bytes()
last=json.loads((B/'XRe_L002/receipt.json').read_text())
assert last['exit_status']==0 and len(last['print_axioms'])==7 and all('sorryAx' not in a for a in last['print_axioms'])
for a in last['print_axioms']:
 if 'depends on axioms:' in a:
  names=set(a.split('[',1)[1].split(']',1)[0].split(', '));assert names<={'propext','Classical.choice','Quot.sound'},a
out=dict(errors=errors,budget_used={'Lean':len(lean),'Kani':len(kani),'Charon_Aeneas':len(translation)},budgets={'Lean':100,'Kani':20,'Charon_Aeneas':4},kani_passed=[r['attempt'] for r in kani if r['exit']==0],kani_failed=[r['attempt'] for r in kani if r['exit']!=0],wall_seconds_sum=sum(r['wall_seconds'] for r in rows),max_peak_rss_kib=max(r['peak_rss_kib'] for r in rows),max_cgroup_peak_bytes=max(r['cgroup_peak_bytes'] for r in rows),swaps_sum=sum(r['swaps'] for r in rows),attempts=rows)
(B/'XRe_Verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['errors','budget_used','kani_passed','kani_failed','max_peak_rss_kib','max_cgroup_peak_bytes','swaps_sum']}));assert not errors
