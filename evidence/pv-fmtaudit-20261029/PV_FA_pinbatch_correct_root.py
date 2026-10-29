from pathlib import Path
import json,re,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
mods=['AeneasMeta.Extensions','Aeneas.Extract.Extract','Aeneas.Std.Primitives','Aeneas.Std.Core.Core','Aeneas.Std.Scalar.Core','Aeneas.Std.Array.Array','Aeneas.Std.Core.Fmt','Aeneas.Std.RawPtr','Aeneas.Std.Slice','Aeneas.Std.Core.Convert','Aeneas.Std.Array.ArraySlice','Aeneas.Std.Scalar.Notations','Aeneas.Std.Core.Discriminant','Aeneas.Std.Core.Iter','Aeneas.Std.Core.Ptr','Aeneas.Std.SliceIter','Aeneas.Std.RangeIter','Aeneas.Data.Discriminant']
pending=set(mods);order=[]
while pending:
 ready=[m for m in mods if m in pending and not(set(re.findall(r'^import (\S+)',(H/'pinned-source/backends/lean'/(m.replace('.','/')+'.lean')).read_text(),re.M))&pending)]
 assert ready,'cycle';m=ready[0];pending.remove(m);order.append(m)
(H/'pin-rebuild-order-correct-root.json').write_text(json.dumps(order,indent=2))
for id,m in enumerate(order,73740):
 receipts=list(H.glob('pincompile-'+str(id)+'*/receipt/receipt.json'))
 if receipts:
  assert all(json.loads(p.read_text())['exit_status']==0 for p in receipts),'previous failed source cannot be rerun'
  continue
 while True:
  refusals=[]
  for d in H.glob('pincompile-'+str(id)+'*'):
   if (d/'receipt/receipt.json').exists():continue
   for f in ['reservation.json','barrier.json']:
    if (d/f).exists() and json.loads((d/f).read_text()).get('allowed')is False:
     refusals.append(str(d));break
  if len(refusals)>=10:
   print('TEN_ADMISSION_REFUSALS',id,refusals,flush=True);sys.exit(78)
  c=H/'admission-not-before.json'
  while c.exists():
   delay=json.loads(c.read_text())['epoch']-time.time()
   if delay<=0:break
   print('COOLDOWN',id,round(delay,1),flush=True);time.sleep(min(55,delay))
  r=subprocess.run([sys.executable,str(H/'PV_FA_launch.py'),'pincompile',str(id),m.replace('.','/')],cwd=H)
  if r.returncode==78:continue
  if r.returncode:sys.exit(r.returncode)
  break
