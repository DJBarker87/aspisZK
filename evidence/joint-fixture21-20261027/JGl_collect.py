from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
records=[];valid={};fail=[]
for n in range(1,101):
 a=f'JGl21_{n:03}';rp=P/a/'receipt.json';cp=P/(a+'.json')
 if not cp.exists():continue
 cfg=json.loads(cp.read_text())
 if rp.exists():
  r=json.loads(rp.read_text());r['receipt_path']=str(rp.relative_to(R));r['charged_attempt']=n
  if r['exit_status']==0:
   for s,h in r['source_hashes'].items():
    q=R/'lean'/s
    if q.exists() and hashlib.sha256(q.read_bytes()).hexdigest()==h:
     valid[s]={'attempt':a,'source_sha256':h,'print_axioms':r['print_axioms']}
  else:fail.append(n)
 else:
  r=dict(charged_attempt=n,attempt=a,target=cfg['sources'][0],source_revision=cfg['source_revision'],exit_status='local source-generation/scp preflight failed; Lean not launched' if n==23 else 'pending or missing receipt',wall_seconds=None,peak_rss_kib=None,swaps=None,print_axioms=[],config_path=str(cp.relative_to(R)))
  fail.append(n)
 records.append(r)
(P/'JGl_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
(P/'JGl_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
actual=[r for r in records if isinstance(r['exit_status'],int)]
summary=dict(charged_lean_attempts=len(records),lean_processes=len(actual),accepted=sum(r['exit_status']==0 for r in actual),failed_or_rejected=fail,kani_runs=0,wall_seconds=sum(r['wall_seconds'] for r in actual),max_rss_kib=max(int(r['peak_rss_kib']) for r in actual),swaps=sum(int(r['swaps']) for r in actual),validated_final_modules=len(valid),head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip())
(P/'JGl_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
