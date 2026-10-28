from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
rows=json.loads((E/'NCD_ALL_PLAN_R2.json').read_text());states={}
for p in sorted(E.glob('NCD_L*/receipt.json')):
 r=json.loads(p.read_text());m=r['module'];src=Path('lean')/(m+'.lean')
 states[m]=r['exit_status']==0 and src.exists() and hashlib.sha256(src.read_bytes()).hexdigest() in r['source_hashes'].values()
template=json.loads((E/'NCD_L037.json').read_text());todo=[];i=90
for row in rows:
 m=row['module']
 if states.get(m):continue
 a=f'NCD_L{i:03d}';i+=1
 assert not (E/(a+'.json')).exists()
 cfg=json.loads(json.dumps(template));cfg.update(attempt=a,module=m,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,reservation_retries=0)
 src='NCD_generated/'+m+'.lean';obj='/home/dombarker/project-offloads/codex-cx-tx2mid-cache-20261028/'+m+'.olean'
 cfg['sources']=[src];cfg['command'][-3:]=[obj,src] if False else cfg['command'][-3:]
 cfg['command']=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NCD_generated','-o',obj,src]
 text=Path(row['path']).read_text();todo.append(dict(**row,cfg=cfg,source=text,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
slots=sum(bool(re.fullmatch(r'NCD_L[0-9]+\.json',p.name)) for p in E.iterdir());assert slots+len(todo)<=120,(slots,len(todo))
plan=dict(states=states,rows=todo,existing_conservative_slots=slots,backend='unchanged S2W_lean_host.py',one_scope_at_a_time=True)
(E/'NCD_batch_plan.json').write_text(json.dumps(plan,indent=2)+'\n');print('pending',len(todo),'conservative reserved total',slots+len(todo))
