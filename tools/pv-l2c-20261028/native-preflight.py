from pathlib import Path
import subprocess,json,hashlib,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
paths=subprocess.check_output(['git','ls-files','crates/aspis-core','crates/aspis-statement','crates/aspis-prover','Cargo.toml','Cargo.lock'],cwd=R,text=True).splitlines()
paths=[p for p in paths if p.endswith(('.rs','.toml','.lock'))]
expected={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths}
code='''import pathlib,sys,json,hashlib
H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027/source');out=[]
for p,want in json.load(sys.stdin).items():
 q=(pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/kani/host_forest.rs') if p=='crates/aspis-prover/src/host_forest.rs' else H/p);h=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None;out.append(dict(path=p,sha256=h,expected=want,match=h==want))
print(json.dumps(out))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(expected),text=True,capture_output=True);assert p.returncode==0,p.stderr
out=json.loads(p.stdout);(E/'native-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
assert all(x['match'] for x in out),[x for x in out if not x['match']]
print('Verified',len(out),'native dependency source/manifests against current worktree; native control gates only')
