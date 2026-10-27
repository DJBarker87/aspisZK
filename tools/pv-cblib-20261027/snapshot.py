"""Upload the frozen candidate's Rust source snapshot, once, with source hashes."""
from pathlib import Path
import subprocess,json,hashlib
root=Path(__file__).resolve().parents[2];host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';out=root/'evidence/pv-cblib-20261027'
r=subprocess.run(['ssh',host,f'python3 {gate}/reservation.py {base}/snapshot-upload.json > {base}/snapshot-upload.log 2>&1; cat {base}/snapshot-upload.log'],text=True,capture_output=True)
(out/'snapshot-upload.log').write_text(r.stdout+r.stderr)
assert r.returncode==0 and json.loads(r.stdout)['allowed']
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/z4']
existing=set(subprocess.check_output(['git','ls-tree','--name-only','HEAD'],cwd=root,text=True).splitlines())
if 'rust-toolchain.toml' in existing:paths.append('rust-toolchain.toml')
assert subprocess.run(['ssh',host,f'test ! -e {base}/source && mkdir {base}/source']).returncode==0
archive=subprocess.Popen(['git','archive','HEAD',*paths],cwd=root,stdout=subprocess.PIPE)
p=subprocess.run(['ssh',host,f'tar -x -C {base}/source'],stdin=archive.stdout);archive.stdout.close();assert archive.wait()==0 and p.returncode==0
files=subprocess.check_output(['git','ls-files',*paths],cwd=root,text=True).splitlines()
r={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'paths':paths,'files':{f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files}}
(out/'candidate-snapshot.json').write_text(json.dumps(r,indent=2)+'\n')
