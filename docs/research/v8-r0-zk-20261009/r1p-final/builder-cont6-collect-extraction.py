#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[3]
script='''import pathlib,json,hashlib
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref6-20261021')
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size,path=str(p))
result={}
for stage in ['admission-common','admission-included','forest-source-p6','nullifier-monomorphic']:
 E=R/stage
 summary=json.loads((E/'summary.json').read_text())
 receipts={}
 for p in sorted(E.glob('*/receipt.json')):
  d=json.loads(p.read_text());folder=p.parent
  d['full_stderr']=(folder/'stderr.log').read_text()
  d['stdout_pin']=pin(folder/'stdout.log')
  d['time_log']=(folder/'time.log').read_text()
  receipts[folder.name]=d
 result[stage]=dict(summary=summary,receipts=receipts,metadata_rename=json.loads((E/'metadata-rename.json').read_text()) if (E/'metadata-rename.json').exists() else None,artifacts={str(p.relative_to(E)):pin(p) for p in E.rglob('*') if p.is_file() and p.suffix in ['.llbc','.lean']})
 if stage=='forest-source-p6':
  data=json.loads((E/'admission.llbc').read_text())['translated']
  ds=[x for x in data['fun_decls'] if x and x['item_meta']['name'][-1]=={'Ident':['records',0]}]
  result[stage]['records_bodies']=[dict(name=x['item_meta']['name'],body=x['body']) for x in ds]
print(json.dumps(result))
'''
d=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
for stage,r in d.items():
 for path,pin in r['summary']['source_pins'].items():
  p=ROOT/path;assert p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256'],(stage,path)
for x in d['forest-source-p6']['records_bodies']: assert x['body'] is None or x['body']=='Opaque',x['body']
d['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
d['caps']=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,RUSTFLAGS='-C link-arg=-Wl,--threads=4')
d['status']='Only admission-included plus the explicit std adaptation is a kernel certificate; all other raw outputs remain diagnostics, not accepted axioms.'
(HERE/'builder-cont6-extraction.json').write_text(json.dumps(d,indent=2)+'\n')
print('PASS: all exact host source pins agree; shipped records body stayed opaque; extraction receipts collected')
