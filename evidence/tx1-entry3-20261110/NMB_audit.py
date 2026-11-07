"""Own audit orchestration; all production scopes retain original exit status."""
from NMB_formal import *
import base64

def recover(mode):
    r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});paths=list((b/'NMB_audit'/{mode!r}).rglob('*'))+list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))
if {mode!r}=='scan':paths.append(b/'NMB_LOADED_scan.jsonl')
out={{}}
for p in paths:
 if p.is_file():
  raw=p.read_bytes();out[str(p.relative_to(b))]={{'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'xz':base64.b64encode(lzma.compress(raw)).decode()}}
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
    out=json.loads(r.stdout);pins={}
    for n,v in out.items():
        p=E/'NMB_raw'/mode/n;p.parent.mkdir(parents=True,exist_ok=True)
        data=base64.b64decode(v.pop('xz'));raw=lzma.decompress(data);assert sha(raw)==v['sha256']
        if p.suffix in ['.json','.time']:p.write_bytes(raw)
        else:p.with_name(p.name+'.xz').write_bytes(data);p.with_name(p.name+'.sha256').write_text(v['sha256']+'\n')
        pins[n]=v
    (E/'NMB_raw'/mode/'NMB_MANIFEST.json').write_text(json.dumps(pins,indent=1)+'\n')
    receipt=E/'NMB_raw'/mode/'NMB_audit'/mode/(mode+'.json')
    return json.loads(receipt.read_text()) if receipt.exists() else None

def link(a,target):
    r=ssh('python3',f"from pathlib import Path;import json;print(json.dumps((Path({B!r})/'NMB_native'/{(target+'.c')!r}).read_text()))");assert r.returncode==0
    files={'NMB_native/'+target+'.c':json.loads(r.stdout)}
    for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NMB_native/'+n]=lzma.decompress((E/('NMB_'+n+'.xz')).read_bytes()).decode()
    T=json.loads((E/'NMB_ENV.json').read_text())['env']['LEAN_SYSROOT']
    return run(a,'link',target,command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMB_native/'+target,*files],extra=files)

def audit(a,mode):
    files={n:(E/n).read_text()for n in ['NMB_audit_batch.py','NMB_AUDIT_ROOTS.json','NMB_AUDIT_MODULES.json','NMB_EXPECTED_IMPORTS.jsonl']}
    rc=run(a,'audit',mode,command=['python3','NMB_audit_batch.py',mode],extra=files)
    child=recover(mode)
    # No rerun on timeout/killed or missing data. Collector discrepancies stay visible.
    if rc['exit_status'] not in [0,1] or child is None:raise RuntimeError('Audit incomplete; isolate only missing work, never resubmit '+a)
    if mode=='scan':assert rc['exit_status']==0
    else:
        roots=json.loads((E/'NMB_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])]if mode.startswith('proof')else None
        results=child['results']
        if roots is not None:
            assert {x['root']for x in results}==set(roots),'Missing raw roots'
            assert all(set(x['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])for x in results),'Nonstandard raw axiom'
        else:
            assert len(results)==8 and all(x['equal']for x in results),'Fixture mismatch'
            assert all(bool(x['walked_axioms'])==(i<4)for i,x in enumerate(results))
    return rc,child

if __name__=='__main__':
    a,kind,target=sys.argv[1:]
    if kind=='link':sys.exit(link(a,target)['exit_status'])
    audit(a,target)
