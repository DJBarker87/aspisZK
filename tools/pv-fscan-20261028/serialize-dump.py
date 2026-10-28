from pathlib import Path
import os,sys,subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');name,profile=sys.argv[1:];P=D/'serialize';P.mkdir(exist_ok=True);O=D/name;O.mkdir(exist_ok=True)
(P/'Cargo.toml').write_text('[package]\nname="pv-fscan-serializer"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[features]\nct=["aspis-core/ct-host-prover"]\n[dependencies]\naspis-core={path="../src/crates/aspis-core",features=["r0"]}\n')
(P/'lib.rs').write_text('pub fn wide_bytes(x: aspis_core::field::WideExact)->[u8;32] {x.to_le_bytes()}\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',RUSTC_BOOTSTRAP='1',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(D/'target'),CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0')
cmd=['cargo','rustc','--manifest-path',str(P/'Cargo.toml'),'--lib','-j','4']
if profile=='release':cmd+=['--release','--features','ct']
cmd+=['--','--emit=mir','-Zmir-opt-level=4'];(O/'command.json').write_text(json.dumps(dict(argv=cmd,env={k:v for k,v in env.items() if k.startswith(('RUST','CARGO'))}),indent=2));r=subprocess.run(cmd,env=env)
if not r.returncode:
 ps=list((D/'target'/('debug' if profile=='dev' else 'release')/'deps').glob('pv_fscan_serializer-*.mir'));p=max(ps,key=lambda p:p.stat().st_mtime);b=p.read_bytes();(O/'crate.mir').write_bytes(b);(O/'mir-identity.json').write_text(json.dumps(dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())))
sys.exit(r.returncode)
