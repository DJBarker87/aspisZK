from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent;H=E/'harness'
spec={
 'call-v1':('oracle27-call-v2.rs',None), 'call-v2':('oracle27-call-v2.rs',None),
 'call-v3':('oracle27-call-v3.rs',None), 'call-v4':('oracle27-call-v4.rs',None),
 'extracted-call-v1':('oracle27-extracted-call-v1.rs','effect27-v2.rs'),
 'extracted-call-v2':('oracle27-extracted-call-v2.rs','effect27-v2.rs'),
 'extracted-call-v3':('oracle27-extracted-call-v3.rs','effect27-v2.rs'),
 'extracted-call-v4':('oracle27-extracted-call-v5.rs','effect27.rs'),
 'different-v1':('oracle27-extracted-call-v5.rs','effect27.rs'),
}
for v in range(1,5):
 for tool in ['charon','aeneas']:
  spec[f'effect-{tool}-v{v}']=(None,'effect27.rs' if v==4 else f'effect27-v{v}.rs')
for tool in ['charon','aeneas']:spec[f'callers-{tool}-v1']=('callers27.rs',None)
rows={}
for name,(main,extra) in spec.items():
 rows[name]=dict(source_base_revision='26b922be6',source_identity='Exact complete owned source snapshot hashes, with pinned extraction/Kani kit and standard library; not an attribution to changed shipped code.',sources={str(H/p):hashlib.sha256((H/p).read_bytes()).hexdigest() for p in [main,extra] if p})
for p in E.glob('*-inputs.json'):
 r=json.loads(p.read_text())
 if 'sources' in r:
  name=p.name[:-len('-inputs.json')]
  rows[name]=dict(source_base_revision='26b922be6',source_revision=r['source_revision'],sources={str(E/'rust-sources'/name/(k+'.txt')):v for k,v in r['sources'].items()})
assert set(rows)=={p.parent.name for p in (E/'receipts').glob('*/receipt.json')}
(E/'rust-inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),'Rust/extraction source identities pinned')
