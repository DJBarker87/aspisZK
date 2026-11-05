from NIS_formal import *
files={n:(E/n).read_text() for n in ['NIS_AUDIT_ROOTS.json','NIS_EXPECTED_IMPORTS.jsonl','NIS_audit_one.py']}
files['NIM_AUDIT_MODULES.json']=json.dumps([['NIS_COMBINED_IMPORT']])
for i,mode,name in [(32,'proof0','NIS_ProofDriver'),(33,'scan','NIS_ScanDriver')]:
    rc=run(f'NIS_L{i:03}','audit',mode,['python3','NIS_audit_one.py','NIS_native/'+name,mode],files)
    if rc['exit_status']:sys.exit(rc['exit_status'])
    r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NIS_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NIS_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text() for p in paths}}))
''');assert r.returncode==0,r.stderr
    for n,t in json.loads(r.stdout).items():
        p=E/('NIS_'+n)
        if n.endswith('.json'):p.write_text(t)
        else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
print('Stage2 raw axioms and NFX scan completed',flush=True)
