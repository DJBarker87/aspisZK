"""Create one byte-pinned library snapshot; append only a cfg(kani) harness."""
from pathlib import Path
import subprocess,json,hashlib,shlex,time
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';host='dombarker@100.108.41.90';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';tag=str(time.time_ns())
r=subprocess.run(['ssh',host,f'python3 {gate}/reservation.py {base}/block-buffer-upload-{tag}.json > {base}/block-buffer-upload-{tag}.log 2>&1; cat {base}/block-buffer-upload-{tag}.log'],text=True,capture_output=True);(out/f'block-buffer-upload-{tag}.log').write_text(r.stdout+r.stderr);assert r.returncode==0 and json.loads(r.stdout)['allowed']
code='''from pathlib import Path
import shutil,hashlib,json
src=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/block-buffer-0.10.4');dest=Path(%r)/'block-buffer-vendor'
assert not dest.exists()
shutil.copytree(src,dest)
r={str(p.relative_to(src)):hashlib.sha256(p.read_bytes()).hexdigest() for p in src.rglob('*') if p.is_file()}
print(json.dumps(r))
'''%base
r=subprocess.check_output(['ssh',host,'python3 -c '+shlex.quote(code)],text=True);(out/'block-buffer-vendor-prefix-hashes.json').write_text(r)
subprocess.run(['scp',str(root/'tools/pv-cblib-20261027/block-buffer-harness.rs'),host+':'+base+'/block-buffer-harness.rs'],check=True)
subprocess.run(['ssh',host,f'cat {base}/block-buffer-harness.rs >> {base}/block-buffer-vendor/src/sealed.rs'],check=True)

subprocess.run(['scp',str(root/'Cargo.lock'),host+':'+base+'/block-buffer-vendor/Cargo.lock'],check=True)
