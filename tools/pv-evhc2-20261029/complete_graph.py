from pathlib import Path
import json,subprocess,re
E=Path('evidence/pv-evhc2-20261029');plan=json.load(open(E/'plan.json'))
events={v['module']:v for v in json.load(open('evidence/pv-evhc-20261029/evh-cohort-pins.json'))}
base=json.loads(subprocess.check_output(['git','show','b51b1040f2:evidence/pv-rj4idb-20261029/source-resolution.json']))['projects']
shared={};missing=[]
for m,s in {**base,**{m:v['source'] for m,v in events.items() if 'source'in v}}.items():
 if 'imports' in s:shared[m]=s['imports'];continue
 b=subprocess.check_output(['git','show',s['revision']+':'+s['path']]).decode()
 shared[m]=re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',re.sub(r'/\-.*?\-/','',b,flags=re.S),re.M)
plan['shared_project_edges']=shared
plan['all_event_pins']={m:dict(path=v['path'],sha256=v['sha256']) for m,v in events.items()}
plan['all_event_pins'].update({m:dict(path=v['path'],sha256=v['sha256']) for m,v in plan['events'].items()})
(E/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print('shared edges',len(shared))
