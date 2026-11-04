from pathlib import Path
import subprocess,json,ast,lzma,hashlib
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/codex-pv-k4trace-20261104';T='2db53bdeb0d396e4bf3263a0d0fdd516c4c0b8a8'
s=subprocess.check_output(['git','show',T+':tools/pv-stx-20261104/context-gate.py']).decode();(E/'original/context-gate.py.txt').write_text(s)
tree=ast.parse(s);text=None
for n in ast.walk(tree):
 if isinstance(n,ast.Assign) and any(isinstance(t,ast.Subscript) and isinstance(t.value,ast.Name) and t.value.id=='files' and isinstance(t.slice,ast.Constant) and t.slice.value=='Cargo.toml' for t in n.targets):text=ast.literal_eval(n.value)
assert text is not None
q=E/'source-payload.json.xz';p=json.loads(lzma.decompress(q.read_bytes()));p['stx/Cargo.toml']=text;q.write_bytes(lzma.compress(json.dumps(p).encode()))
q=E/'source-provenance.json';p=json.loads(q.read_text());p['stx/Cargo.toml']={'revision':T,'path':'tools/pv-stx-20261104/context-gate.py','method':'exact literal files[Cargo.toml] from the original source preparation script','sha256':hashlib.sha256(text.encode()).hexdigest()};q.write_text(json.dumps(p,indent=2)+'\n')
q=E/'runs.json';p=json.loads(q.read_text())
for r in p:
 if r['credit'].startswith('K931'):r['pins']['Cargo.toml']=hashlib.sha256(text.encode()).hexdigest()
 if r['id']=='K93509':r['id']='K93513'
q.write_text(json.dumps(p,indent=2)+'\n')
code='''from pathlib import Path
import hashlib,json
original=Path('/home/dombarker/project-offloads/codex-pv-stx-20261104/native-source/Cargo.toml')
text=TEXT
assert hashlib.sha256(text.encode()).hexdigest()=='55235c7451062fc29d599b94c23f9488b8ebfc8acbde3bd6a158afe12b07eb0e'
q=Path(ROOT)/'sources/stx/Cargo.toml';assert not q.exists();q.write_text(text)
print(json.dumps({'source':str(original),'recovered_from':'2db53bdeb0d:tools/pv-stx-20261104/context-gate.py literal','sha256':hashlib.sha256(text.encode()).hexdigest(),'matches_original_context_stage_pin':True,'current_host_sha256':hashlib.sha256(original.read_bytes()).hexdigest()}))
'''.replace('TEXT',repr(text)).replace('ROOT',repr(H))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr;(E/'workspace-recovery.json').write_text(r.stdout)
print(r.stdout)
