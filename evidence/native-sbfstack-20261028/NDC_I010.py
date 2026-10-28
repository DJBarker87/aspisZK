from pathlib import Path
import hashlib,json,subprocess
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028');out={'resolved_native_tools':{},'runtime_registry_checks':{}}
for name in ['rustc','cargo']:
 q=subprocess.run(['/home/dombarker/.cargo/bin/rustup','which',name],cwd=H,capture_output=True,text=True);assert q.returncode==0,q.stderr
 p=Path(q.stdout.strip());out['resolved_native_tools'][name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
for crate in ['solana-sbpf-0.21.1','solana-program-runtime-4.2.1','solana-bpf-loader-program-4.2.1','solana-syscalls-4.2.1']:
 d=reg/crate;j=json.loads((d/'.cargo-checksum.json').read_text());files={};snap=json.loads((H/'NDC_RUNTIME_SOURCES.json').read_text())
 for key,v in snap.items():
  p=Path(key)
  if d not in p.parents:continue
  rel=str(p.relative_to(d))
  if rel not in j['files']:continue
  actual=hashlib.sha256(p.read_bytes()).hexdigest();files[rel]={'sha256':actual,'expected':j['files'][rel],'matches':actual==j['files'][rel]};assert actual==j['files'][rel]
 out['runtime_registry_checks'][crate]={'package_checksum':j['package'],'files':files}
out['own_native_target_absent']=not (H/'NDC_target_native').exists();assert out['own_native_target_absent']
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
out['limits']={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max','memory.peak','memory.swap.peak']}
(H/'NDC_FINAL_PROVENANCE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
