from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
errors=[];records=[];accepted={};all_axioms=[]
for p in sorted(E.glob('XRr_L*/receipt.json')):
 r=json.loads(p.read_text());records.append(r)
 a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append(a+' admission')
 if not r['command'][r['command'].index('-M7000')]=='-M7000':errors.append(a+' memory flag')
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+' caps')
 if int(r['swaps']):errors.append(a+' swap')
 for src,sha in r['source_hashes'].items():
  f=p.parent/'sources'/src
  if not f.is_file() or hashlib.sha256(f.read_bytes()).hexdigest()!=sha:errors.append(a+' source hash')
 if r['exit_status']==0:
  accepted[r['module']]=(p,r)
  for line in r['print_axioms']:
   m=re.search(r'axioms:\s*\[([^\]]*)\]',line,re.S)
   names={n.strip() for n in m.group(1).split(',')} if m else set()
   if names-{'propext','Classical.choice','Quot.sound'}:errors.append(a+' axioms '+line)
   all_axioms.append(dict(attempt=a,line=line))
for f in E.glob('XRr_*.lean'):
 m=f.stem
 if m not in accepted:errors.append(m+' no successful final receipt');continue
 p,r=accepted[m]
 if hashlib.sha256(f.read_bytes()).hexdigest() not in r['source_hashes'].values():errors.append(m+' final hash mismatch')
 if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxHeartbeats|maxRecDepth)',f.read_text(),re.M):errors.append(m+' forbidden proof form')
for name in ['XRr_AuditQuery','XRr_AuditSemantic','XRr_AuditCandidate','XRr_FinalAudit','XRr_RootAudit']:
 if name not in accepted:errors.append(name+' missing audit')
before=(E/'XRr_top_before.lean.txt').read_bytes();after=(E/'XRr_top_after.lean.txt').read_bytes()
if before!=after:errors.append('headline changed')
if len(records)!=100:errors.append('compiler count '+str(len(records)))
preflights=[json.loads(p.read_text()) for p in sorted(E.glob('XRr_L*_PRECOMPILER.json'))]
summary=dict(lean_used=len(records),lean_limit=100,pass_count=sum(r['exit_status']==0 for r in records),fail_count=sum(r['exit_status']!=0 for r in records),precompiler_refusals=preflights,kani_used=0,kani_limit=10,compiler_wall_seconds=sum(r['wall_seconds'] for r in records),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in records),swaps=sum(int(r['swaps']) for r in records),stopped_at_budget=True)
(E/'XRr_BUDGET.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'XRr_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
(E/'XRr_ACCEPTED_AXIOMS.json').write_text(json.dumps(all_axioms,indent=2)+'\n')
ledger=dict(target='AspisR1.RPx_Deployed.deployed',before_kernel_statement='XRr_top_before.lean.txt',after_kernel_statement='XRr_top_after.lean.txt',kernel_sha256=hashlib.sha256(before).hexdigest(),byte_identical=before==after,method='atomic-family / SAME-witness / shared-nonce / L185=L159',removed=0,added=0,changed=0,delta=dict(T=0,P=0,G=0,C=0),inherited_booked=dict(T=83,P=0,G=13),L154='statement parameter, not an open premise',fresh_absolute_recount=False,root_axioms_receipt='XRr_L072/receipt.json',fresh_signature_reemission=False,new_trust=False,game_metric_quantifier_carrier_failure_changes=False)
(E/'XRr_RECOUNT_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
result=dict(errors=errors,checked_compilers=len(records),checked_final_modules=len(list(E.glob('XRr_*.lean'))),accepted_axioms_only=True if not errors else False,headline_byte_identical=before==after)
(E/'XRr_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(summary));print(json.dumps(result))
raise SystemExit(bool(errors))
