"""Build audit copies with one additive input-capture call; never edit final sources."""
from pathlib import Path
import json,hashlib,subprocess,os,re
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe';O=H/'audit-src';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for side,stem,sub in [('user','user_client','user_client'),('fixture','devnet_spend','devnet_spend')]:
 root=C/'src/bin'/(stem+'.rs');plan=C/'src/bin'/sub/'plan.rs';s=plan.read_text()
 # Resolve child account modules to the unchanged actual files.
 s=re.sub(r'#\[path="([^"]+)"\]',lambda m:'#[path='+json.dumps(str(plan.parent/m[1]))+']',s)
 needle=' let result=RealR1_client::prove_for_proof_accounts';assert s.count(needle)==1
 s=s.replace(needle,' super::audit_export::capture(dir,&compiled);\n'+needle)
 (O/(side+'-plan.rs')).write_text(s)
 root_s=re.sub(r'#\[path="([^"]+)"\]',lambda m:'#[path='+json.dumps(str(O/(side+'-plan.rs') if m[1]==sub+'/plan.rs' else root.parent/m[1]))+']',root.read_text())
 root_s+='\n#[path='+json.dumps(str(H/'audit_export.rs'))+']\nmod audit_export;\n'
 (O/(side+'.rs')).write_text(root_s)
 rows.append(dict(side=side,source_root=str(root),source_root_sha256=sha(root),source_plan=str(plan),source_plan_sha256=sha(plan),audit_root_sha256=sha(O/(side+'.rs')),audit_plan_sha256=sha(O/(side+'-plan.rs')),change='absolute module paths plus single additive capture(dir,&compiled) immediately before unchanged RealR1 call; no source or branch removed'))
s=C.joinpath('Cargo.toml').read_text().replace('default-run = "aspis-r1-cu-probe"','autobins = false')
s=re.sub(r'path = "../../([^"]+)"',lambda m:'path = '+json.dumps(str(H/'src'/m[1])),s)
for side in ['user','fixture']:s+='\n[[bin]]\nname = "pv-uc-'+side+'-audit"\npath = '+json.dumps(str(O/(side+'.rs')))+'\n'
(O/'Cargo.toml').write_text(s);(O/'Cargo.lock').write_bytes((C/'Cargo.lock').read_bytes())
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--manifest-path',str(O/'Cargo.toml'),'--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bins']
r=subprocess.run(c,env=e)
x=dict(exit=r.returncode,command=c,source_copies=rows,export_source_sha256=sha(H/'audit_export.rs'),lock_byte_equal=(O/'Cargo.lock').read_bytes()==(C/'Cargo.lock').read_bytes(),binaries={p.name:sha(p) for p in (H/'native-target/client').glob('pv-uc-*-audit')})
(H/'final-gates/audit-build.json').write_text(json.dumps(x,indent=2)+'\n');raise SystemExit(r.returncode)
