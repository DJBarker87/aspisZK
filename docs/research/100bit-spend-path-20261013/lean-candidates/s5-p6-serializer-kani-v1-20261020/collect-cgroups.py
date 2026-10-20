import os,json,pathlib,datetime
root=pathlib.Path('/sys/fs/cgroup')
rows=[]
for dp,ds,fs in os.walk(root):
 p=pathlib.Path(dp); ev=p/'cgroup.events'; mxp=p/'memory.max'; curp=p/'memory.current'
 if not ev.exists() or not mxp.exists(): continue
 try:
  evs=dict(line.split() for line in ev.read_text().splitlines() if len(line.split())==2)
  if evs.get('populated')!='1': continue
  mx=mxp.read_text().strip(); cur=int(curp.read_text().strip()) if curp.exists() else None
  rows.append({'path':str(p),'max':mx,'current_bytes':cur,'scope':p.name.endswith('.scope')})
 except (PermissionError,ValueError): pass
finite=[r for r in rows if r['max']!='max']
finite_paths={pathlib.Path(r['path']) for r in finite}
effective=[]
for r in finite:
 p=pathlib.Path(r['path']); parent=p.parent; covered=False
 while parent!=root.parent and parent!=p:
  if parent in finite_paths: covered=True; break
  if parent==root: break
  parent=parent.parent
 if not covered: effective.append(r)
unbounded_scopes=[r for r in rows if r['scope'] and r['max']=='max']
mi={x.split(':')[0]:int(x.split()[1]) for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if ':' in x}
out={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'MemTotal_kB':mi['MemTotal'],'MemAvailable_kB':mi['MemAvailable'],'SwapTotal_kB':mi['SwapTotal'],'SwapFree_kB':mi['SwapFree'],'populated_cgroups':len(rows),'finite_nodes':finite,'effective_reservation_nodes':effective,'effective_sum_bytes':sum(int(r['max']) for r in effective),'unbounded_populated_scopes':unbounded_scopes,'all_populated_cgroups':rows}
print(json.dumps(out,indent=2))
