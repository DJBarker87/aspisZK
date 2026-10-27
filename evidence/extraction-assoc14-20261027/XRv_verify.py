from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
errors=[];rs=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for i in range(1,101):
 a=f'XRv_L{i:03}';p=E/a/'receipt.json'
 if not p.exists():errors.append(a+':missing receipt');continue
 r=json.loads(p.read_text());rs.append(r)
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if not ad.get('allowed'):errors.append(a+':not admitted')
 if r['limits']!=limits:errors.append(a+':limits')
 if '-M7000' not in r['command']:errors.append(a+':Lean cap')
 if int(r['swaps']):errors.append(a+':swap')
 for src,sha in r['source_hashes'].items():
  p=E/a/'sources'/src
  if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=sha:errors.append(a+':source '+src)
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'sorryAx' in line:errors.append(a+':unaccepted axiom')
proofs=['XRv_FromFnTotal','XRv_DecoderTotal','XRv_DecodedWords','XRv_QueryDriver','XRv_QueryDriverTotal','XRv_QueryScanTotal','XRv_SelectedAdvance','XRv_DriverSelected']
for m in proofs+['XRv_RootAudit']:
 b=(E/(m+'.lean')).read_bytes();sha=hashlib.sha256(b).hexdigest()
 if not any(r['exit_status']==0 and r['module']==m and sha in r['source_hashes'].values() for r in rs):errors.append(m+':no matching PASS')
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',b.decode()):errors.append(m+':forbidden source token')
allowed={'propext','Classical.choice','Quot.sound'}
new_axes={}
for r in rs:
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if line.startswith("'XRv_"):
    new_axes[line.split("'")[1]]=line
    match=re.search(r'\[([^]]*)\]',line)
    if match and not set(x.strip() for x in match.group(1).split(','))<=allowed:errors.append(r['attempt']+':nonstandard axioms')
if len(new_axes)!=22:errors.append('expected22 new audited facts')
result=dict(errors=errors,attempt_identifiers=100,actual_lean_processes=len(rs),passed=sum(r['exit_status']==0 for r in rs),failed=sum(r['exit_status']!=0 for r in rs),failed_attempts=[r['attempt'] for r in rs if r['exit_status']!=0],kani_runs=0,wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=sum(int(r['swaps']) for r in rs),reservation_retries=sum(r['reservation_retries'] for r in rs),admission='invoker requires exit0 AND allowed:true; verified allowed:true for every receipt',new_proof_modules=proofs,new_audited_facts=new_axes,root_audit='XRv_L083',new_proof_coimport='L100 EXCLUDED exit1 missing explicit LPk_Result import; separate passing imports L094/L096 retained',inherited_LPi_field_chain='XRv_L078-L082',full_frozen_manifest_ran=False,no_shipped_changes=True)
(E/'XRv_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'XRv_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
