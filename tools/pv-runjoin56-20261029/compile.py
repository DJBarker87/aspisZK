"""Own replay wrapper: admission, single capped chunk, original receipts and no resubmit."""
from pathlib import Path
import subprocess,json,shlex,sys,time,datetime,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin56-20261029';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';P=H+'/runjoin32-lean';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);idx=int(sys.argv[2]);assert 68200<=a<=68299
plan=json.loads((E/'build-plan.json').read_text());mods=sys.argv[3:] or plan['chunks'][idx]
assert all(m in plan['modules'] for m in mods),'stage every target before admission'
assert len(mods)==1,'one module per attempt'
for prior in (R/'evidence').glob('pv-runjoin*/modules-*.json'):
 for record in json.loads(prior.read_text()):
  if not record['accepted']:
   assert record['source_sha256']!=plan['modules'][mods[0]]['sha256'],('unchanged failed source forbidden',record['module'],str(prior))
assert len(list(E.glob('receipt-*.json')))<100
assert not (E/f'submission-{a}.json').exists(),'submitted already; recover read-only'
# Own-input gate: a newly staged dependency must have an accepted matching source.
round_sources={m:v for m,v in plan['modules'].items() if m.startswith('R1Z.PV_RunJoin_') and m.endswith(('52','53','54','55','56'))}
round_accepted={v['module']:v for p in list((R/'evidence/pv-runjoin52-20261029').glob('modules-*.json'))+list((R/'evidence/pv-runjoin53-20261029').glob('modules-*.json'))+list((R/'evidence/pv-runjoin54-20261029').glob('modules-*.json'))+list((R/'evidence/pv-runjoin55-20261029').glob('modules-*.json'))+list(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
for m in mods:
 for d in plan['modules'][m]['imports']:
  if d in round_sources:
   assert d in round_accepted and round_accepted[d]['source_sha256']==round_sources[d]['sha256'],('compile prerequisite first',m,d)

def transport(cmd,**kw):
 for k in range(11):
  r=subprocess.run(cmd,**kw)
  if r.returncode!=255:return r
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=k,command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
  if k==10:raise RuntimeError('10 transport retries exhausted')
  print('transport unavailable; 60s retry cooldown',flush=True);time.sleep(60)
def ssh(cmd):return transport(['ssh',host,cmd],text=True,capture_output=True)
active=ssh("systemctl --user list-units --plain --no-legend --state=running 'pv*-lean-*'")
assert active.returncode==0 and not active.stdout.strip(),('own scope still running; collect completion before next launch',active.stdout,active.stderr)
prior=list(E.glob('refusal-*.json'))
if prior:
 deadline=max(json.loads(p.read_text())['epoch'] for p in prior)+180
 if time.time()<deadline:
  print('unlaunched cooldown remaining',deadline-time.time(),flush=True);sys.exit(77)
# Ruling o: refresh cross-job receipt and sent-table check for THIS ID.
id_code=r"""import pathlib,re,json
root=pathlib.Path('/home/dombarker/project-offloads');hits=[];a=ATTEMPT
pat=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)')
for job in root.glob('codex-pv-*'):
 if job.name=='codex-pv-runjoin-20261026':continue
 for q in job.glob('evidence/**/*'):
  if len(q.relative_to(job).parts)<=6 and q.is_file() and pat.search(q.name):hits.append(str(q))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]==str(a)]
print(json.dumps(dict(attempt=a,other_receipt_hits=hits,sent_hits=lines)))
""".replace('ATTEMPT',str(a))
id_result=ssh('python3 -c '+shlex.quote(id_code));assert id_result.returncode==0,id_result.stderr
id_audit=json.loads(id_result.stdout);(E/f'id-audit-{a}.json').write_text(json.dumps(id_audit,indent=2)+'\n')
assert not id_audit['other_receipt_hits'] and not id_audit['sent_hits'],id_audit

cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv56-lean-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',P+f'/evidence/time-{a}.log','python3',P+'/chunk-host.py',P,str(a),json.dumps(mods)]
intent=dict(attempt=a,chunk=idx,modules=mods,source_revision=plan['modules'][mods[0]].get('revision',plan['source_revision']) if len(mods)==1 else plan['source_revision'],source_revisions={m:plan['modules'][m].get('revision',plan['source_revision']) for m in mods},wrapper_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,reservation=None,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),old_objects_written=False,external_ir_companions_sha256=hashlib.sha256((E/'external-ir-companions.json').read_bytes()).hexdigest() if (E/'external-ir-companions.json').exists() else None)
(E/f'submission-{a}.json').write_text(json.dumps(intent,indent=2)+'\n')
print('LAUNCH',a,'chunk',idx,len(mods),'modules',flush=True)
# Never retry this SSH call; a lost connection requires original-log recovery.
start=time.monotonic()
admit=f'python3 {H}/reservation-existing.py {P}/evidence/reservation-{a}.json > {P}/evidence/reservation-{a}.log 2>&1'
check="python3 -c "+shlex.quote("import json; assert json.load(open("+repr(P+f'/evidence/reservation-{a}.json')+"))['allowed'] is True")
remote='bash -o pipefail -c '+shlex.quote(admit+' && '+check+' && '+shlex.join(cmd)+f' 2>&1 | tee {P}/evidence/out-{a}.log')
proc=subprocess.Popen(['ssh',host,remote],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
stream=[];done_count=0
for line in proc.stdout:
 stream.append(line)
 if line.startswith('DONE'):done_count+=1
 if line.startswith(('DONE','CHUNK','RECEIPT')):print(line.rstrip(),flush=True)
rc=proc.wait()
class Result:pass
r=Result();r.returncode=rc
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=rc,stdout=''.join(stream),stderr='',wall=time.monotonic()-start),indent=2)+'\n')
q=ssh(f'cat {P}/evidence/reservation-{a}.json');assert q.returncode==0,q.stderr
admission=json.loads(q.stdout);(E/f'reservation-{a}.json').write_text(q.stdout)
q=ssh(f'cat {P}/evidence/reservation-{a}.log');(E/f'reservation-{a}-{time.time_ns()}.log').write_text(q.stdout+q.stderr)
if not admission.get('allowed') or rc!=0:
 q=ssh(f'test -f {P}/evidence/results-{a}.json');started=q.returncode==0
 if not started:
  admission.update(epoch=time.time(),attempt=a,compiler_started=False,admission_exit=rc)
  (E/f'refusal-{a}-{time.time_ns()}.json').write_text(json.dumps(admission,indent=2)+'\n')
  (E/f'submission-{a}.json').rename(E/f'unlaunched-submission-{a}-{time.time_ns()}.json')
  if 'error' in admission:
   assert re.search(r'(?:FileNotFoundError|OSError): \[Errno (?:2|19)\]',admission['error']),admission
   assert sum('error' in json.loads(p.read_text()) for p in E.glob(f'refusal-{a}-*.json'))<=3,'fourth scan race'
  print('REFUSED uncharged; same ID after full 180s cooldown', {k:admission.get(k) for k in ['attempt','allowed','admission_exit','compiler_started','error']},flush=True);sys.exit(78)
assert admission.get('allowed') is True,'VOID launch'
intent['reservation']=admission
intent['admission_exit']=0
intent['admission_and_launch_same_shell']=True
intent['cooldown_checked_before_launch']=True
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

if not intent['accepted']:print(out[-7000:],flush=True)
print('RECEIPT',json.dumps({k:intent[k] for k in ['attempt','accepted','completed_modules','failed_module','host_wall_seconds','peak_rss_bytes','swaps']}),flush=True)
sys.exit(0 if intent['accepted'] else 1)
