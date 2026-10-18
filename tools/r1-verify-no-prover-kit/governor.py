#!/usr/bin/env python3
"""Task-specific native governor. Foreign activity record-only under user parallel override."""
import argparse,fcntl,hashlib,json,os,signal,subprocess,time
from datetime import datetime,timezone
from pathlib import Path
BLOCKED={'lean','lake','cargo','rustc','charon','charon-driver','aeneas','cargo-build-sbf','cargo-build-bpf','solana-test-validator','ld.lld','rust-lld','lld','ld','cc','clang','gcc','clang++','g++'}
LOCK='/tmp/aspis-r1-worker-b-native.lock';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blocked_executable(name):
 name=name.lower()
 return name in BLOCKED or name.startswith(('charon','aeneas','aspis','solana-','r1-','r1_')) or any(x in name for x in ['aspis','charon','aeneas','pool','replay'])
def classify(records,own,dedicated_cgroup=None):
 def ours(pid):
  seen=set()
  while pid in records and pid not in seen:
   if pid==own:return True
   seen.add(pid);pid=records[pid]['ppid']
  return False
 return sorted([{**p,'pid':pid} for pid,p in records.items() if blocked_executable(p['exe']) and not ours(pid) and not (dedicated_cgroup is not None and p.get('cgroup')==dedicated_cgroup)],key=lambda p:p['pid'])
def foreign_jobs(dedicated_cgroup=None):
 procs={}
 for d in Path('/proc').iterdir():
  if not d.name.isdigit():continue
  try:
   stat=(d/'stat').read_text().split(') ',1)[1].split();procs[int(d.name)]={'ppid':int(stat[1]),'exe':(d/'exe').resolve().name,'start_ticks':stat[19],'command':(d/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')[:1800],'cgroup':(d/'cgroup').read_text().strip()}
  except (OSError,ValueError,IndexError):pass
 return classify(procs,os.getpid(),dedicated_cgroup)
def reservation_snapshot(own_cgroup=None):
 finite=[]
 for path in Path('/sys/fs/cgroup').rglob('memory.max'):
  directory=path.parent
  try:
   value=path.read_text().strip();events=(directory/'cgroup.events').read_text();relative='0::/'+str(directory.relative_to('/sys/fs/cgroup'))
   if value=='max' or 'populated 1' not in events or relative==own_cgroup:continue
   finite.append({'path':str(directory),'MemoryMax_bytes':int(value),'memory_current_bytes':int((directory/'memory.current').read_text()),'cgroup':relative})
  except OSError:continue
 # A finite ancestor reservation covers its child scopes; do not double count.
 top=[item for item in finite if not any(item['path'].startswith(other['path']+'/') for other in finite if other!=item)]
 total=sum(item['MemoryMax_bytes'] for item in top);return {'other_populated_finite_cgroup_reservations':sorted(top,key=lambda p:p['path']),'other_MemoryMax_bytes':total,'proposed_own_MemoryMax_bytes':8*2**30,'sum_with_own_bytes':total+8*2**30,'safe_working_limit_bytes':55*2**30,'admitted':total+8*2**30<=55*2**30,'rule':'All finite populated cgroup reservations, including services; nested finite ancestor covers children; exact dedicated own scope excluded.'}
def cgroup_metrics(cg):
 return {n:(cg/n).read_text().strip() for n in ['memory.current','memory.peak','memory.swap.current','memory.events']}
def stop_own_group(pid):
 try:os.killpg(pid,signal.SIGKILL)
 except ProcessLookupError:pass
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--label',required=True);a.add_argument('--execute-granted',action='store_true');args=a.parse_args();root=args.root.resolve();kit=root/'tools/r1-verify-no-prover-kit';pins=json.loads((kit/'source-pins.json').read_text());gate=next(g for g in pins['gates'] if g['label']==args.label);command=[x.replace('{root}',str(root)) for x in gate['command']];journal=root/'governor';journal.mkdir(exist_ok=True);dest=journal/(args.label+('-execute' if args.execute_granted else '-preflight')+'.json');assert not dest.exists(),'retain old governor receipt; choose another root/label before retry';entry={'label':args.label,'utc_start':datetime.now(timezone.utc).isoformat(),'source_revision':pins['after_revision'],'source_pins_sha256':sha(kit/'source-pins.json'),'governor_sha256':sha(__file__),'shared_lock':LOCK,'command':command,'execute_granted':args.execute_granted,'foreign_process_samples':[],'policy_override':{'source':'User instruction: just do it in parallel; root coordination clarification 2026-10-18','foreign_activity':'record only; never blocks or stops a B job by itself','own_jobs':'B phase lock serializes B native gates; A may run concurrently','admission':'Own6G high/8G max/swap0; aggregate populated finite-cgroup MemoryMax plus proposed B8G must be <=55GiB before and continuously during own job.'}}
 def save():dest.write_text(json.dumps(entry,sort_keys=True,indent=2)+'\n')
 with open(LOCK,'a+') as lock:
  try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  except BlockingIOError:entry['status']='SUPPRESSED_LOCK_BUSY_NO_CHILD';save();return 75
  cgtext=Path('/proc/self/cgroup').read_text().strip();dedicated=None;cg=None
  if args.execute_granted:
   assert cgtext.startswith('0::');cg=Path('/sys/fs/cgroup')/cgtext[3:].lstrip('/');assert cg.name=='r1-b-no-prover-'+args.label+'-20261018.scope','Exact dedicated scope required; never exempt a broad user prefix';limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'};dedicated=cgtext;entry['limits']=limits;entry['cgroup']=cgtext;entry['cgroup_before']=cgroup_metrics(cg)
  entry['aggregate_reservations']=reservation_snapshot(dedicated)
  if not entry['aggregate_reservations']['admitted']:entry['status']='SUPPRESSED_AGGREGATE_MEMORYMAX_NO_CHILD';save();return 75
  arrivals=foreign_jobs(dedicated);entry['foreign_process_samples'].append({'utc':datetime.now(timezone.utc).isoformat(),'processes':arrivals})
  if not args.execute_granted:entry['status']='PREFLIGHT_CLEAR_NO_CHILD';save();print(json.dumps(entry));return 0
  manifest=root/'inputs.json';m=json.loads(manifest.read_text());assert m['source_revision']==pins['after_revision'];assert all(sha(root/n)==h for n,h in m['files'].items());assert sha(kit/'run-host.py')=='d011230e71adac99208489591e770e92744e53f9117be18060e315770866bb8c'
  runner=['python3',str(kit/'run-host.py'),'--root',str(root),'--input-manifest',str(manifest),'--label',args.label,'--cwd',str(root/'source'),'--kind','native','--timeout','600','--',*command]
  # Lock and process check are in the same launcher as the actual child spawn.
  arrivals=foreign_jobs(dedicated)
  entry['foreign_process_samples'].append({'utc':datetime.now(timezone.utc).isoformat(),'processes':arrivals})
  admission=reservation_snapshot(dedicated);entry['immediately_before_spawn_reservations']=admission
  if not admission['admitted']:entry['status']='SUPPRESSED_AGGREGATE_BEFORE_SPAWN_NO_CHILD';save();return 75
  started=time.monotonic();last_monitor=started;last_foreign=[(p['pid'],p['start_ticks']) for p in arrivals];child=subprocess.Popen(runner,start_new_session=True);entry['own_process_group']=child.pid;save()
  while child.poll() is None:
   if time.monotonic()-last_monitor>=1:
    last_monitor=time.monotonic();arrivals=foreign_jobs(dedicated);identity=[(p['pid'],p['start_ticks']) for p in arrivals]
    if identity!=last_foreign:entry['foreign_process_samples'].append({'utc':datetime.now(timezone.utc).isoformat(),'processes':arrivals});last_foreign=identity
    current=reservation_snapshot(dedicated);entry['last_aggregate_reservations']=current
    if not current['admitted']:
     entry['status']='STOPPED_OWN_GROUP_UNSAFE_AGGREGATE_MEMORYMAX';entry['unsafe_aggregate_reservations']=current;stop_own_group(child.pid);break
   if time.monotonic()-started>660:entry['status']='STOPPED_OWN_GROUP_GOVERNOR_TIMEOUT';stop_own_group(child.pid);break
   time.sleep(.2)
  entry['exit_status']=child.wait();entry['cgroup_after']=cgroup_metrics(cg);entry['wall_seconds']=time.monotonic()-started;entry['utc_end']=datetime.now(timezone.utc).isoformat();entry.setdefault('status','OWN_JOB_EXITED');save();print(json.dumps(entry));return entry['exit_status'] or (76 if entry['status'].startswith('STOPPED') else 0)
if __name__=='__main__':raise SystemExit(main())
