from pathlib import Path
import importlib.util,json
B=Path('/home/dombarker/project-offloads')
w=B/'aspis-r1-j1a-terminal-public-joint-20261016'
roots=[B/'aspis-r1-j17-port-20261015/extracted',B/'aspis-r1-j1a-terminal-proof-20261016',B/'aspis-r1-j1a-terminal-caller-adapted-20261016']
s=importlib.util.spec_from_file_location('r',w/'runner.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
base=roots[0]/'external-inputs-002.json';d,_=r.verify_snapshot(base)
ms={p:json.loads((p/'sources/SOURCE-MANIFEST.json').read_text()) for p in roots}
ss={roots[0]:d,roots[1]:d,roots[2]:r.verify_snapshot(roots[2]/'external-inputs-terminal.json')[0]}
ks={p:r.external_keys(v) for p,v in ss.items()};audit=[]
def visit(n):
 if n in d['modules']:return
 hits=[p for p,m in ms.items() if n in m['modules']];assert len(hits)==1,(n,hits)
 p=hits[0];item=ms[p]['modules'][n];src=p/'sources'/item['stage_as'];assert r.sha(src)==item['source_sha256']
 deps=r.imports(src,implicit_init=True)
 for dep in deps:visit(dep)
 rp=p/'successful-targets'/(n+'.json');rec=json.loads(rp.read_text());assert rec['exit_status']==0 and rec['axioms']['passed']
 assert rec['key']['source_sha256']==r.sha(src) and rec['key']['runtime']==d['runtime_files'] and rec['key']['options']==['-j1','-M0']
 obj=r.object_pins(p/'objects',n,d['olean_header_seal']);assert obj==rec['objects']
 expected={}
 for dep in deps:
  if dep in ms[p]['modules']:
   dr=json.loads((p/'successful-targets'/(dep+'.json')).read_text());expected[dep]={'receipt_key':r.digest(dr['key']),'objects':r.object_pins(p/'objects',dep,d['olean_header_seal'])}
  else:expected[dep]={'objects':ss[p]['modules'][dep]['objects'],'closure_key':ks[p][dep]}
  assert d['modules'][dep]['objects']==expected[dep]['objects'],(n,dep,'different object dependency')
 assert rec['key']['imports']==expected,n
 rn='checked_'+str(roots.index(p));d['modules'][n]={'root':rn,'source':str(src),'source_sha256':r.sha(src),'imports':deps,'objects':obj,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 audit.append({'module':n,'source':str(src),'source_sha256':r.sha(src),'receipt':str(rp),'receipt_sha256':r.sha(rp),'objects':obj})
for n in ['ExtractedTerminalCallerBridge','ExtractedPublicCheckedBridge432']:visit(n)
for i,p in enumerate(roots):d['roots'].insert(0,{'name':'checked_'+str(i),'source':str(p/'sources'),'objects':str(p/'objects')})
d['provenance_files'][str(base)]=r.sha(base)
(w/'input-manifests').mkdir(exist_ok=True)
for i,p in enumerate(roots):
 q=w/'input-manifests'/('origin'+str(i)+'.json');r.dump(q,ms[p]);d['provenance_files'][str(q)]=r.sha(q)
d['scope']='Exact receipt extension for Terminal/current Caller/public joint diagnostic; source/import/runtime/object hashes checked, including every direct imported object.'
r.dump(w/'external-inputs-joint.json',d);r.dump(w/'import-source-audit.json',audit)
n='TerminalPublicJointImport';src=w/'sources'/(n+'.lean')
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':{n:{'stage_as':n+'.lean','source':'diagnostic/'+n+'.lean','source_sha256':r.sha(src),'source_revision':'2ff2ea148','imports':r.imports(src),'role':'Joint import only','axiom_requests':0}},'topological_order':[n],'groups':{}})
r.staged(w);print(json.dumps({'modules_added':len(audit),'snapshot_sha256':r.sha(w/'external-inputs-joint.json')},indent=2))
