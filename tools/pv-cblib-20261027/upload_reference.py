from pathlib import Path
import subprocess,time,json
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';host='dombarker@100.108.41.90';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';tag=str(time.time_ns())
r=subprocess.run(['ssh',host,f'python3 {gate}/reservation.py {base}/reference-upload-{tag}.json > {base}/reference-upload-{tag}.log 2>&1; cat {base}/reference-upload-{tag}.log'],text=True,capture_output=True);(out/f'reference-upload-{tag}.log').write_text(r.stdout+r.stderr)
if r.returncode or not json.loads(r.stdout)['allowed']:raise SystemExit(78)
subprocess.run(['scp',str(root/'tools/pv-cblib-20261027/lib.rs'),f'{host}:{base}/source-proof/lib.rs'],check=True)

subprocess.run(['scp',str(root/'tools/pv-cblib-20261027/Cargo.toml'),f'{host}:{base}/source-proof/Cargo.toml'],check=True)
