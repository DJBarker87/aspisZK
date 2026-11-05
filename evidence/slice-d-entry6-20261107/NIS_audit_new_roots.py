from NIS_formal import *
files={n:(E/n).read_text() for n in ['NIS_AUDIT_ROOTS.json','NIS_EXPECTED_IMPORTS.jsonl','NIS_audit_one.py']};files['NIM_AUDIT_MODULES.json']=json.dumps([['NIS_COMBINED_IMPORT'],['NIS_COMBINED_IMPORT']])
r=run('NIS_L062','audit','proof1',['python3','NIS_audit_one.py','NIS_native/NIS_ProofDriver','proof1'],files);assert r['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_proof1_*_REACHABLE.txt'))+[b/'NIS_binary_proof1.json']
print(json.dumps({{p.name:p.read_text() for p in paths}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/('NIS_'+n)
 if n.endswith('.json'):p.write_text(t)
 else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
print('PASS_ADDITIONAL_RAW_GROUP',flush=True)
