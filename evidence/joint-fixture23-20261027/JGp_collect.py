from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
records=[];valid={};failed=[]
for n in range(1,101):
 a=f'JGp23_{n:03}';cp=P/(a+'.json');rp=P/a/'receipt.json'
 if not cp.exists():continue
 cfg=json.loads(cp.read_text())
 if rp.exists():
  d=json.loads(rp.read_text());d.update(charged_attempt=n,receipt_path=str(rp.relative_to(R)))
  if d['exit_status']==0:
   assert all('sorryAx' not in x for x in d['print_axioms'])
   for s,h in d['source_hashes'].items():
    f=R/'lean'/s
    if f.exists() and hashlib.sha256(f.read_bytes()).hexdigest()==h:
     valid[s]=dict(attempt=a,source_sha256=h,print_axioms=d['print_axioms'])
  else:failed.append(n)
 elif n==75:
  d=json.loads((P/'JGp23_075-PREFLIGHT.json').read_text());failed.append(n)
 else:
  d=dict(charged_attempt=n,attempt=a,exit_status='pending or missing receipt',target=cfg['sources'][0]);failed.append(n)
 records.append(d)
(P/'JGp_ATTEMPTS.jsonl').write_text(''.join(json.dumps(d)+'\n' for d in records))
(P/'JGp_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
actual=[d for d in records if isinstance(d['exit_status'],int)]
summary=dict(charged_lean_attempts=len(records),lean_processes=len(actual),accepted=sum(d['exit_status']==0 for d in actual),failed_or_rejected=failed,kani_runs=0,wall_seconds=sum(d['wall_seconds'] for d in actual),max_rss_kib=max(int(d['peak_rss_kib']) for d in actual),swaps=sum(int(d['swaps']) for d in actual),validated_final_modules=len(valid),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),branch=subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip())
(P/'JGp_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
manifest=[]
for f in sorted(P.glob('JGp23_*/**/*')):
 if f.is_file():manifest.append(dict(path=str(f.relative_to(R)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
(P/'JGp_RECORDS_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(summary,indent=2))
