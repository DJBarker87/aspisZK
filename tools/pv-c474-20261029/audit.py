from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');R=H/'src'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin')
for name,cwd,features in [('client',R/'tools/r1-cost-probe','r1p-check,aspis-r1-cost-probe/ct-host-prover'),('probes',R,'optimized-terminal,r1p-check,ct-host-prover')]:
 cmd=['cargo','+1.94.1','metadata','--locked','--offline','--format-version','1','--features',features]
 if name=='probes':cmd+=['--filter-platform','x86_64-unknown-linux-gnu']
 r=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,check=True);m=json.loads(r.stdout)
 packages={p['id']:p for p in m['packages']}
 graph=[dict(name=packages[n['id']]['name'],version=packages[n['id']]['version'],manifest_path=packages[n['id']]['manifest_path'],features=n['features'],dependencies=n['dependencies']) for n in m['resolve']['nodes']]
 (H/(name+'-resolved-features.json')).write_text(json.dumps(graph,indent=2)+'\n')
source={}
paths=['/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src/backtrace.rs','/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/anyhow-1.0.104/src/backtrace.rs','/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4/src/backends/linux_raw.rs','/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4/src/backends.rs']
for p0 in paths:
 p=Path(p0)
 if not p.exists():
  # registry directory hash is installation-specific, never version-substitute.
  hits=list(Path('/home/dombarker/.cargo/registry/src').glob('*/'+p0.split('index.crates.io-1949cf8c6b5b557f/')[1]));assert len(hits)==1; p=hits[0]
 dest=H/('source-'+p.parent.name+'-'+p.name+'.txt');dest.write_bytes(p.read_bytes());source[str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),snapshot=dest.name)
client=H/'native-target/client/devnet_spend'
r=dict(client_sha256=hashlib.sha256(client.read_bytes()).hexdigest(),client_bytes=client.stat().st_size,toolchain=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],text=True),source_pins=source,profiles='client inherits release, panic abort; on-chain root release unchanged',no_project_force_capture=subprocess.run(['rg','-n','force_capture',str(R/'crates'),str(R/'programs'),str(R/'tools/r1-cost-probe/src/bin/devnet_spend')],capture_output=True,text=True).returncode==1)
(H/'audit-result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

# Source files named by the fresh client-profile dep-info, including dependencies.
selected=set()
for dep in (H/'native-target/client/deps').glob('*.d'):
 for word in dep.read_text().replace('\\\n',' ').split():
  p=Path(word.rstrip(':'))
  if p.suffix=='.rs' and p.is_absolute() and p.is_file():selected.add(p)
hits=[]
for p in sorted(selected):
 for i,line in enumerate(p.read_text().splitlines(),1):
  if 'force_capture' in line:hits.append(dict(path=str(p),line=i,text=line))
(H/'force-capture-scan.json').write_text(json.dumps(dict(depinfo_selected_source_files=len(selected),hits=hits),indent=2)+'\n')
print('force_capture hits',json.dumps(hits),flush=True)
