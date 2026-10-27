from pathlib import Path
import subprocess,json,hashlib,time
root=Path(__file__).resolve().parents[2];base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';host='dombarker@100.108.41.90';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';out=root/'evidence/pv-cblib-20261027'
p='crates/aspis-r1-cost-probe/src/host_commitment.rs';before=subprocess.check_output(['git','show','bd47052f039ae2d96060acb5607fe652ebe193d4:'+p],cwd=root);after=(root/p).read_bytes()
assert after.startswith(before) and after[len(before):].lstrip().startswith(b'#[cfg(kani)]\nmod pv_cblib_library_checks')
tag=str(time.time_ns())
r=subprocess.run(['ssh',host,f'python3 {gate}/reservation.py {base}/kani-upload-{tag}.json > {base}/kani-upload-{tag}.log 2>&1; cat {base}/kani-upload-{tag}.log'],text=True,capture_output=True);(out/f'kani-upload-{tag}.log').write_text(r.stdout+r.stderr)
if r.returncode or not json.loads(r.stdout)['allowed']:raise SystemExit(78)
subprocess.run(['ssh',host,f'mkdir -p {base}/kani-proof'],check=True)
for src,dest in [(root/p,base+'/source/'+p),(root/'tools/pv-cblib-20261027/kani-lib.rs',base+'/kani-proof/lib.rs'),(root/'tools/pv-cblib-20261027/kani-Cargo.toml',base+'/kani-proof/Cargo.toml')]:
 subprocess.run(['scp',str(src),host+':'+dest],check=True)
(out/'kani-source-map.json').write_text(json.dumps({'source':p,'frozen_prefix_sha256':hashlib.sha256(before).hexdigest(),'cfg_kani_snapshot_sha256':hashlib.sha256(after).hexdigest(),'frozen_prefix_bytes':len(before),'added_bytes':len(after)-len(before),'production_change':False},indent=2)+'\n')
