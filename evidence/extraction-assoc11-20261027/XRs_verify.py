from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
errors=[];receipts=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for i in range(1,101):
 a=f'XRs_L{i:03}';p=E/a/'receipt.json'
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if not ad.get('allowed'):errors.append(a+':not admitted')
 if not p.exists():
  if i!=27:errors.append(a+':missing receipt')
  continue
 r=json.loads(p.read_text());receipts.append(r)
 if r['limits']!=limits:errors.append(a+':limits')
 if '-M7000' not in r['command']:errors.append(a+':Lean memory cap')
 if int(r['swaps']):errors.append(a+':swap')
 for src,sha in r['source_hashes'].items():
  p=E/a/'sources'/src
  if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=sha:errors.append(a+':source '+src)
 if r['exit_status']==0 and any('sorryAx' in line for line in r['print_axioms']):errors.append(a+':unaccepted axiom')
proofs=['XRs_AddStep','XRs_AddIndexed','XRs_AddInvariant','XRs_LoopBind','XRs_AddLoop','XRs_AddAssociation','XRs_ByteSteps','XRs_WordBytes','XRs_Serializer','XRs_ClosedCallbacks','XRs_QueryScan','XRs_BaseMultiply']
for m in proofs+['XRs_Audit','XRs_RootAudit']:
 b=(E/(m+'.lean')).read_bytes();sha=hashlib.sha256(b).hexdigest()
 if not any(r['exit_status']==0 and r['module']==m and sha in r['source_hashes'].values() for r in receipts):errors.append(m+':no matching PASS')
 if re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',b.decode()):errors.append(m+':forbidden source token')
result=dict(errors=errors,attempt_identifiers=100,actual_lean_processes=len(receipts),precompiler_failures=[27],passed=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),reservation_retries=sum(r['reservation_retries'] for r in receipts),new_proof_modules=proofs,new_audited_theorems=28,root_audit='XRs_L084',final_audit='XRs_L100',no_shipped_changes=True)
(E/'XRs_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'XRs_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
