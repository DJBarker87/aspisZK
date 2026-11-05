from NIS_formal import *
for i,name in [(26,'NIS_ProofDriver'),(27,'NIS_ScanDriver')]:
    rc=run(f'NIS_L{i:03}','lean',name)
    if rc['exit_status']:sys.exit(rc['exit_status'])
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for i,name in [(28,'NIS_ProofDriver'),(29,'NIS_ScanDriver')]:
    r=ssh('cat '+B+'/NIS_native/'+name+'.c');assert r.returncode==0
    files={'NIS_native/'+name+'.c':r.stdout}
    for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NIS_native/'+n]=lzma.decompress((E/('NIS_'+n+'.xz')).read_bytes()).decode()
    rc=run(f'NIS_L{i:03}','link',name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NIS_native/'+name,*files],files)
    if rc['exit_status']:sys.exit(rc['exit_status'])
for i,mode,name in [(30,'fixtures','NIS_ProofDriver'),(31,'proof0','NIS_ProofDriver'),(32,'scan','NIS_ScanDriver')]:
    files={n:(E/n).read_text() for n in ['NIS_AUDIT_ROOTS.json','NIS_EXPECTED_IMPORTS.jsonl']}
    rc=run(f'NIS_L{i:03}','audit',mode,['NIS_native/'+name,mode],files)
    if rc['exit_status']:sys.exit(rc['exit_status'])
    # Retain every raw walker edge file and the full scanner output, compressed.
    r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))
if {mode!r}=='scan':paths+=[b/'NIS_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths}}))
''');assert r.returncode==0,r.stderr
    for n,t in json.loads(r.stdout).items():
        p=E/('NIS_'+n);p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
print('Stage2 raw axioms, fidelity fixtures and NFX scan completed',flush=True)
