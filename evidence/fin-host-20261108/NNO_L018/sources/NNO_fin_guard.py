"""Pause a FIN compile above 1 GiB RSS; inspect before any continuation."""
from pathlib import Path
import subprocess,sys,time,os,signal,json
p=subprocess.Popen(sys.argv[2:]);B=Path.cwd();name=sys.argv[1];inspected=False
while p.poll()is None:
 ids=[p.pid];cursor=0
 while cursor<len(ids):
  pid=ids[cursor];cursor+=1
  try:ids.extend(int(x)for x in (Path('/proc')/str(pid)/'task'/str(pid)/'children').read_text().split())
  except(FileNotFoundError,ProcessLookupError):pass
 candidates=[]
 for pid in ids:
  try:
   raw=(Path('/proc')/str(pid)/'status').read_text();size=next((int(l.split()[1])for l in raw.splitlines()if l.startswith('VmRSS:')),0);candidates.append((size,pid))
  except(FileNotFoundError,ProcessLookupError):pass
 watched=max(candidates,default=(0,p.pid))[1]
 status=Path('/proc')/str(watched)/'status'
 try:
  d={k:v.strip()for k,v in (l.split(':',1)for l in status.read_text().splitlines()if ':'in l)}
  rss=int(d.get('VmRSS','0 kB').split()[0])
  if rss>1048576 and not inspected:
   os.kill(watched,signal.SIGSTOP);time.sleep(.1)
   d={k:v.strip()for k,v in (l.split(':',1)for l in status.read_text().splitlines()if ':'in l)}
   maps=(Path('/proc')/str(watched)/'maps').read_text();anon=int(d.get('RssAnon','0 kB').split()[0]);files=int(d.get('RssFile','0 kB').split()[0])
   decision='resume_same_process_same_caps'if anon<1048576 and files>anon else'stop_anonymous_memory_growth'
   receipt=dict(pid=watched,status=d,mapped_objects=[l for l in maps.splitlines()if'.olean'in l or'.ir'in l],decision=decision,reason='Inspect imported object mappings versus anonymous elaboration memory; no restart and no cap change')
   (B/(name+'-memory-review.json')).write_text(json.dumps(receipt,indent=1)+'\n');inspected=True
   if decision.startswith('resume'):os.kill(watched,signal.SIGCONT)
   else:os.kill(watched,signal.SIGKILL);break
 except(FileNotFoundError,ProcessLookupError):pass
 time.sleep(.025)
sys.exit(p.wait())
