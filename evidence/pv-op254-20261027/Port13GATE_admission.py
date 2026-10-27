#!/usr/bin/env python3
"""Full cgroup-v2 population inventory. No process-name or user-tree filter."""
import datetime,json,pathlib,sys
CAP=8*1024**3
LIMIT=55*1024**3

def snapshot(root):
 root=pathlib.Path(root)
 rows=[]
 def walk(p,ancestor=None):
  # Do not skip empty subtrees: retain them in the inventory, and detect races.
  # cgroup-v2 intentionally omits cgroup.events and memory.max at the root.
  events=({'populated':'1'} if p==root else
    dict(line.split() for line in (p/'cgroup.events').read_text().splitlines()))
  populated=int(events['populated']);assert populated in (0,1)
  if p==root:
   row={'path':str(p.relative_to(root)), 'populated':populated,'root':True}
   bounded=ancestor
  else:
   controllers=(p/'cgroup.controllers').read_text().split()
   memory_enabled='memory' in controllers
   parent_controllers=(p.parent/'cgroup.subtree_control').read_text().split()
   assert memory_enabled==('memory' in parent_controllers),str(p)
   ctype=(p/'cgroup.type').read_text().strip()
   process_file='cgroup.threads' if ctype=='threaded' else 'cgroup.procs'
   values={'cgroup.procs':(p/process_file).read_text().strip(),'cgroup.type':ctype,
      'direct_ids_source':process_file}
   if memory_enabled:
    values.update({f:(p/f).read_text().strip() for f in
      ['memory.max','memory.high','memory.swap.max','memory.current']})
   else:
    assert not (p/'memory.max').exists(),str(p)
    values.update({'memory.max':'max','memory.high':None,'memory.swap.max':None,
      'memory.current':None,'memory_controller':'disabled; inherited ancestor accounting'})
   maximum=values['memory.max'];assert maximum=='max' or int(maximum)>=0
   row={'path':str(p.relative_to(root)),'populated':populated,**values}
   row['direct_process_count']=len(values.pop('cgroup.procs').splitlines())
   row.pop('cgroup.procs',None)
   bounded=ancestor
   if populated and maximum!='max' and ancestor is None:
    bounded=row['path'];row['reservation_bytes']=int(maximum)
   row['covering_capped_ancestor']=ancestor
  rows.append(row)
  for child in sorted(p.iterdir()):
   if child.is_dir():walk(child,bounded)
 walk(root)
 total=sum(r.get('reservation_bytes',0) for r in rows)
 return {'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
   'root':str(root),'all_cgroups':rows,'reserved_bytes':total,'additional_bytes':CAP,
   'limit_bytes':LIMIT,'admitted':total+CAP<LIMIT,
   'uncapped_populated':[r['path'] for r in rows if r['populated'] and not r.get('root')
     and r['memory.max']=='max' and r['covering_capped_ancestor'] is None]}

def main():
 try:
  result=snapshot('/sys/fs/cgroup')
  marker=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
  if marker.exists():
   import time
   quiet=json.loads(marker.read_text())
   if time.time()<float(quiet['until']): result.update(admitted=False,quiet_window=quiet)
  result['allowed']=result['admitted']
  print(json.dumps(result,indent=2))
  return 0 if result['allowed'] else 78
 except Exception as exc:
  print(json.dumps({'allowed':False,'admitted':False,'error':str(exc),'fail_closed':True}));return 2
if __name__=='__main__':sys.exit(main())
