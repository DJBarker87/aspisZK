"""Install only the published release bundle and a private rustup toolchain."""
from pathlib import Path
import json,urllib.request,hashlib,subprocess,os
b=Path(__file__).resolve().parent;release=json.loads((b/'KMX_LATEST_RELEASE.json').read_text())
a=next(a for a in release['assets'] if a['name'].endswith('x86_64-unknown-linux-gnu.tar.gz'))
root=b/'KMX_latest';root.mkdir(exist_ok=True);archive=root/a['name']
if not archive.exists():urllib.request.urlretrieve(a['browser_download_url'],archive)
sha=hashlib.sha256(archive.read_bytes()).hexdigest()
assert not a.get('digest') or a['digest']=='sha256:'+sha
bundle=root/release['tag_name']
if not (bundle/'rust-toolchain-version').exists():subprocess.run(['tar','zxf',str(archive),'-C',str(root)],check=True)
version=(bundle/'rust-toolchain-version').read_text().strip()
env=os.environ.copy();env['RUSTUP_HOME']=str(root/'rustup');env['RUSTUP_TOOLCHAIN']=version
subprocess.run(['/home/dombarker/.cargo/bin/rustup','toolchain','install',version,'--profile','minimal'],env=env,check=True)
actual=root/'rustup/toolchains'/version
if not actual.exists():
 matches=list((root/'rustup/toolchains').glob(version+'*'));assert len(matches)==1,matches;actual=matches[0]
link=bundle/'toolchain'
if not link.exists():link.symlink_to(actual)
env['PATH']=str(bundle/'bin')+':'+str(bundle/'pyroot/bin')+':'+env['PATH'];env['PYTHONPATH']=str(bundle/'pyroot')
r=subprocess.run(['kani','--version'],executable=str(bundle/'bin/kani-driver'),env=env,text=True,capture_output=True)
print(r.stdout,r.stderr,flush=True);assert r.returncode==0
cbmc=subprocess.check_output([str(bundle/'bin/cbmc'),'--version'],text=True).strip()
out=dict(tag=release['tag_name'],bundle_sha256=sha,url=a['browser_download_url'],rust_toolchain=version,driver=str(bundle/'bin/kani-driver'),env={k:env[k] for k in ['RUSTUP_HOME','RUSTUP_TOOLCHAIN','PATH','PYTHONPATH']},version=r.stdout.strip(),cbmc=cbmc)
(b/'KMX_LATEST_INSTALL.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
