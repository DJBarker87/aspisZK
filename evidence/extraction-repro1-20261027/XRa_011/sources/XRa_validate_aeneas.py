from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent
p=B/'XRa_historical.llbc'
assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()=='cca010037fefc042d1df364a05edbbf1547ad4cc8bd476bfc14f450f79433b89'
a=B/'XRa_toolchain/aeneas/src/_build/default/main.exe'
assert hashlib.file_digest(a.open('rb'),'sha256').hexdigest()=='2bf381b8d76bed64988ae57079b73c6c119a8f42f23a1e71775081ca66e20309'
cmd=[str(a),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1PublicPreparation','-dest',str(B/'XRa_historical_rebuilt'),'-subdir','AspisR1PublicPreparation','-split-files','-emit-json',str(p)]
print('COMMAND',json.dumps(cmd),flush=True)
r=subprocess.run(cmd);rows=[]
expected={'Types.lean':'bb4ccfd7a77b6e45de16181113c888febda2ecf8c23bdad55c1919fe92762c3e','Funs.lean':'f4aee2661033aeaf820623a7decb3687e2617ae50a2ad4b41e78b253025a1de1'}
for p in sorted((B/'XRa_historical_rebuilt').rglob('*')):
 if p.is_file():
  h=hashlib.sha256(p.read_bytes()).hexdigest();rows.append({'path':str(p.relative_to(B)),'sha256':h,'bytes':p.stat().st_size,'expected':expected.get(p.name),'match':h==expected[p.name] if p.name in expected else None})
(B/'XRa_historical_reproduction.json').write_text(json.dumps({'exit':r.returncode,'outputs':rows},indent=2)+'\n')
print(json.dumps(rows),flush=True)
assert r.returncode==0 and all(x['match'] for x in rows if x['expected']) and len([x for x in rows if x['expected']])==2
