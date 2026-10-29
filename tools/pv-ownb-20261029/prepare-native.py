from pathlib import Path
import subprocess,json,hashlib,base64
R=Path(__file__).resolve().parents[2];D='/home/dombarker/project-offloads/codex-pv-ownb-20261029';E=R/'evidence/pv-ownb-20261029'
records=[]
for rel in ['crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs','crates/aspis-core/src/field/mod.rs','crates/aspis-core/src/field/qm31.rs']:
 p=R/rel
 if p.exists():records.append(dict(path=rel,host_path='/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/'+rel,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip()))
j=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources=records)
code=r'''from pathlib import Path
import json,re,shutil,base64
D=Path(DIR);base=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028')
p=D/'probe';p.mkdir(exist_ok=True)
s=(base/'weights-fixture/Cargo.toml').read_text()
s=re.sub(r'\[\[bin\]\]\nname="[^"]+"\npath="[^"]+"\n','',s)
s+='\n[[bin]]\nname="layout_probe"\npath="probe.rs"\n'
(p/'Cargo.toml').write_text(s)
shutil.copy2(base/'weights-fixture/Cargo.lock',p/'Cargo.lock')
for f in ['deployed-units.json','deployed-client-Cargo.lock']:shutil.copy2(base/f,D/f)
'''.replace('DIR',repr(D))
for rel,target in [('tools/pv-ownb-20261029/layout.rs','probe/probe.rs'),('tools/pv-ownb-20261029/native.py','native.py')]:
 b=(R/rel).read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+rel])
 code+=f"(D/{target!r}).write_bytes(base64.b64decode({base64.b64encode(b).decode()!r}))\n"
code+=f"(D/'native-inputs.json').write_text({json.dumps(j,indent=2)!r})\n"
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True);assert r.returncode==0
(E/'native-inputs.json').write_text(json.dumps(j,indent=2)+'\n')
