"""Read only compiler identity/target audit; writes only the PCH cache."""
import json, pathlib, subprocess, hashlib, shutil, time
B=pathlib.Path('/home/dombarker/project-offloads/codex-pc-reach1-cache-20261110')
assert shutil.disk_usage(B).free >= 40_000_000_000
out={'disk_free_before_bytes':shutil.disk_usage(B).free,'tools':{},'no_build_launched':True}
for label,p in [('retained_sbf','/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/bin/rustc'),('required_native','/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc')]:
 q=pathlib.Path(p); d={'path':p,'exists':q.is_file()}
 if q.is_file():
  d['sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
  r=subprocess.run([p,'--version','--verbose'],capture_output=True,text=True); d.update(version_exit=r.returncode,version=r.stdout,stderr=r.stderr)
  r=subprocess.run([p,'--print','target-list'],capture_output=True,text=True); d.update(target_list_exit=r.returncode,sbf_targets=[t for t in r.stdout.splitlines() if 'bpf' in t],target_list_sha256=hashlib.sha256(r.stdout.encode()).hexdigest())
 out['tools'][label]=d
out['toolchains']=[p.name for p in pathlib.Path('/home/dombarker/.rustup/toolchains').iterdir() if p.is_dir()]
(B/'PCH_HOST_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print('PCH compiler identity audit complete; no compilation')
