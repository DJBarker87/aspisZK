"""Own replay wrapper: admission, single capped chunk, original receipts and no resubmit."""
from pathlib import Path
import subprocess,json,shlex,sys,time,datetime,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';P=H+'/runjoin32-lean';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);idx=int(sys.argv[2]);assert 51300<=a<=51499
plan=json.loads((E/'build-plan.json').read_text());mods=sys.argv[3:] or plan['chunks'][idx]
assert len(list(E.glob('receipt-*.json')))<100
assert not (E/f'submission-{a}.json').exists(),'submitted already; recover read-only'
def transport(cmd,**kw):
 for k in range(11):
  r=subprocess.run(cmd,**kw)
  if r.returncode!=255:return r
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=k,command=cmd,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
  if k==10:raise RuntimeError('10 transport retries exhausted')
  print('transport unavailable; 60s retry cooldown',flush=True);time.sleep(60)
def ssh(cmd):return transport(['ssh',host,cmd],text=True,capture_output=True)
prior=list(E.glob('refusal-*.json'))
if prior:
 deadline=max(json.loads(p.read_text())['epoch'] for p in prior)+180
 if time.time()<deadline:
  print('unlaunched cooldown remaining',deadline-time.time(),flush=True);sys.exit(77)
# Keep attempts fail-closed and check both admission signals.
r=ssh(f'python3 {H}/reservation-existing.py {P}/evidence/reservation-{a}.json > {P}/evidence/reservation-{a}.log 2>&1\nstatus=$?\ncat {P}/evidence/reservation-{a}.log\nexit $status')
(E/f'reservation-{a}-{time.time_ns()}.log').write_text(r.stdout+r.stderr)
try:admission=json.loads(r.stdout.strip().splitlines()[-1])
except Exception:raise RuntimeError('barrier output invalid: '+r.stdout+r.stderr)
if r.returncode!=0 or not admission.get('allowed'):
 admission.update(epoch=time.time(),attempt=a,compiler_started=False)
 (E/f'refusal-{a}-{time.time_ns()}.json').write_text(json.dumps(admission,indent=2)+'\n')
 if 'error' in admission:
  assert re.search(r'(?:FileNotFoundError|OSError): \[Errno (?:2|19)\]',admission['error']),admission
  assert sum('error' in json.loads(p.read_text()) for p in E.glob(f'refusal-{a}-*.json'))<=3,'fourth scan race'
 print('REFUSED uncharged same ID after cooldown',admission,flush=True);sys.exit(78)
transport(['scp','-q',host+':'+P+f'/evidence/reservation-{a}.json',str(E/f'reservation-{a}.json')],check=True)
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv32-lean-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',P+f'/evidence/time-{a}.log','python3',P+'/chunk-host.py',P,str(a),json.dumps(mods)]
intent=dict(attempt=a,chunk=idx,modules=mods,source_revision=plan['source_revision'],wrapper_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,reservation=admission,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),old_objects_written=False,external_ir_companions_sha256=hashlib.sha256((E/'external-ir-companions.json').read_bytes()).hexdigest() if (E/'external-ir-companions.json').exists() else None)
(E/f'submission-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
print('LAUNCH',a,'chunk',idx,len(mods),'modules',flush=True)
# Never retry this SSH call; a lost connection requires original-log recovery.
start=time.monotonic()
remote='bash -o pipefail -c '+shlex.quote(shlex.join(cmd)+f' 2>&1 | tee {P}/evidence/out-{a}.log')
proc=subprocess.Popen(['ssh',host,remote],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
stream=[]
for line in proc.stdout:
 stream.append(line)
 if line.startswith(('START','DONE','CHUNK','RECEIPT')):print(line.rstrip(),flush=True)
rc=proc.wait()
class Result:pass
r=Result();r.returncode=rc
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=rc,stdout=''.join(stream),stderr='',wall=time.monotonic()-start),indent=2)+'\n')
for n in ['out','time']:
 q=ssh(f'cat {P}/evidence/{n}-{a}.log');assert q.returncode==0,q.stderr
 (E/f'{n}-{a}.log').write_text(q.stdout)
q=ssh(f'cat {P}/evidence/results-{a}.json');assert q.returncode==0,'no compiler-result receipt; recover before another launch'
records=json.loads(q.stdout);(E/f'modules-{a}.json').write_text(json.dumps(records,indent=2)+'\n')
tim=(E/f'time-{a}.log').read_text();out=(E/f'out-{a}.log').read_text();get=lambda pat:re.search(pat,tim)
ex=get(r'Exit status: (\d+)');rss=get(r'Maximum resident set size \(kbytes\): (\d+)');swap=get(r'Swaps: (\d+)');elapsed=get(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)');wall=0
if elapsed:
 for c in elapsed[1].split(':'):wall=wall*60+float(c)
intent.update(exit=int(ex[1]) if ex else None,host_wall_seconds=wall,peak_rss_bytes=int(rss[1])*1024 if rss else None,swaps=int(swap[1]) if swap else None,completed_modules=len(records),accepted=bool(ex and int(ex[1])==0 and len(records)==len(mods) and all(v['accepted'] for v in records)),failed_module=next((v['module'] for v in records if not v['accepted']),None),axioms=[line for v in records for line in v['axioms']],axiom_note='Per-module original #print axioms retained; empty means no print in that unchanged source. Root audits follow rebuild.')
(E/f'receipt-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
print(out[-3500:],flush=True);print('RECEIPT',json.dumps({k:intent[k] for k in ['attempt','accepted','completed_modules','failed_module','host_wall_seconds','peak_rss_bytes','swaps']}),flush=True)
sys.exit(0 if intent['accepted'] else 1)
