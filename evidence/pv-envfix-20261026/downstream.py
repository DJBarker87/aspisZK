import subprocess,pathlib,json,re
p=pathlib.Path(__file__).parent;rev=json.loads((p/'audit.json').read_text())['research_revision'];base='docs/research/v8-r0-zk-20261009/lean/'
s=subprocess.check_output(['git','grep','-n','^import ',rev,'--',base],text=True)
g={}
for line in s.splitlines():
 _,path,n,text=line.split(':',3)
 m=path[len(base):-5];g.setdefault(m,[]).extend(z.replace('.','/') for z in text.split()[1:])
target='R1Z/PrivacyR1HeadlineDeployedReal';roots=['R1Z/EventsR1P2','R1Z/SimCostOuterRetry6']
def reach(root):
 seen={root}
 while True:
  more={m for m,ds in g.items() if any(d in seen for d in ds)}-seen
  if not more:return seen
  seen|=more
def ancestors(m,seen):
 if m in seen:return
 seen.add(m)
 for d in g.get(m,[]):ancestors(d,seen)
a=set();ancestors(target,a)
r={m:{'all_downstream':sorted(reach(m)-{m}),'path_to_headline':sorted((reach(m)-{m})&a)} for m in roots}
(p/'downstream.json').write_text(json.dumps({'revision':rev,'roots':r,'imports':g},indent=2)+'\n')
for m,row in r.items():
 print(m,'downstream',len(row['all_downstream']),'on headline path',len(row['path_to_headline']))
 print('\n'.join(row['path_to_headline']))
