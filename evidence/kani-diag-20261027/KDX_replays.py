from pathlib import Path
import json,re,sys,subprocess,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
# Own source parser, used only to copy exact selected functions and named helpers.
ns={'__file__':str(E/'KDX_analyze.py')};exec((E/'KDX_analyze.py').read_text().split('out=[];review=[]')[0],ns);functions=ns['functions']
sources=json.loads((E/'KDX_SOURCE_SNAPSHOTS.json').read_text())['sources'];rows=json.loads((E/'KDX_PASS_INVENTORY.json').read_text())
plans=[('LPa_K004','compact',35),('LPa_K005','compact',17),('LPa_K007','compact',17),('LPa_K015','candidate',35),('LPg_K011','compact',33),('LPg_K012','compact',33),('LPh_K018','compact',33),('LPh_K019','compact',33),('LPh_K020','compact',33),('LPh_K021','compact',33),('LPl_K015','compact',33),('LPn_K001','compact',33),('LPn_K010','r1_wire',33),('LPm_K001','verifier',1025),('LPm_K004','verifier',1769)]
payload={};out=[]
for i,(orig,parent,bound) in enumerate(plans,6):
 row=next(x for x in rows if '/'+orig+'/' in x['receipt']);name=row['harnesses'][0].split('::')[-1]
 # Prefer the file defining the selected proof over unrelated parent modules.
 module=next(v for sha,v in sources.items() if sha in row['source_hashes'].values() and re.search(r'fn\s+'+name+r'\s*\(',v['text']))
 fs=functions(module['text']);todo=[name];seen=set()
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k)
  for call in re.findall(r'\b(\w+)\b',fs[k]['body']):
   if call in fs and call not in seen:todo.append(call)
 m='KDX_R_'+orig
 text='use super::*;\nuse aspis_core::field::CM31;\n'
 for k in sorted(seen):
  if k==name:text+=f'#[kani::proof]\n#[kani::unwind({bound})]\n'
  text+=fs[k]['body']+'\n'
 # Namespacing preserves the selected body and assumptions. Every helper belongs to KDX module.
 text=re.sub(r'\b(?:LP[a-t]|NB[A-M])_',lambda m:'KDX_'+m[0],text)
 name=re.sub(r'\b(?:LP[a-t]|NB[A-M])_',lambda m:'KDX_'+m[0],name)
 path='crates/aspis-r1-cost-probe/src/'+m+'.rs';payload[path]=text;(E/(m+'.rs.txt')).write_text(text)
 full=('verifier::candidate' if parent=='candidate' else parent)+'::'+m+'::'+name
 out.append(dict(attempt=f'KDX_K{i:03}',original=orig,receipt=row['receipt'],harness=full,parent=parent,module=m,path=path,bound=bound,original_source_sha256=hashlib.sha256(module['text'].encode()).hexdigest(),helpers=sorted(seen)))
# Restore parents to exact frozen source, then add cfg-only module declarations.
for parent in {x['parent'] for x in out}:
 path='crates/aspis-r1-cost-probe/src/'+parent+'.rs';text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
 for x in out:
  if x['parent']==parent:text+='\n#[cfg(kani)]\n#[path="'+x['module']+'.rs"]\nmod '+x['module']+';\n'
 payload[path]=text
(E/'KDX_REPLAY_PLAN.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'KDX_replay_payload.json').write_text(json.dumps(payload))
h.admit('KDX_REPLAYUPLOAD')
r=subprocess.run(['scp',str(E/'KDX_replay_payload.json'),h.H+':'+h.B+'/KDX_replay_payload.json'],capture_output=True,text=True);assert r.returncode==0,r.stderr
r=h.remote_py(f'''from pathlib import Path
import json
b=Path({h.B!r});s=b/'KDX_src'
for name,text in json.loads((b/'KDX_replay_payload.json').read_text()).items():
 p=s/name
 if p.is_symlink():p.unlink()
 p.write_text(text)
print('installed KDX-only replay modules')''');assert r.returncode==0,r.stderr
print(r.stdout)
