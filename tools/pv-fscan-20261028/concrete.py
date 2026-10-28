from pathlib import Path
import os,subprocess,sys,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');name,tc=sys.argv[1:];P=D/'concrete';P.mkdir(exist_ok=True);O=D/name;O.mkdir(exist_ok=True)
manifest='''[package]
name="pv-fscan-concrete"
version="0.0.0"
edition="2021"
[workspace]
[lib]
path="lib.rs"
[dependencies]
aspis-core={path="../src/crates/aspis-core",features=["r0","ct-host-prover"]}
aspis-statement={path="../src/crates/aspis-statement",features=["r0","pool-v1-kernel"]}
sha2="=0.10.9"
''';(P/'Cargo.toml').write_text(manifest)
source='''use aspis_core::field::{M31,QM31,WideExact};
use aspis_core::r0::scalar::CodeField;
pub fn parse(x:&[u8])->Option<QM31>{QM31::from_le_bytes(x)}
pub fn qinv(x:QM31)->Option<QM31>{<QM31 as CodeField>::try_inv(x)}
pub fn winv(x:WideExact)->Option<WideExact>{<WideExact as CodeField>::try_inv(x)}
pub fn context_eq(a:&aspis_core::state_only_hiding::StateOnlyHidingContext,b:&aspis_core::state_only_hiding::StateOnlyHidingContext)->bool{a==b}
pub fn statement_eq(a:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1,b:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1)->bool{a==b}
pub fn sha_default()->sha2::Sha256{Default::default()}
''';(P/'lib.rs').write_text(source);(O/'lib.rs.txt').write_text(source);(O/'Cargo.toml.txt').write_text(manifest)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN=tc,RUSTC_BOOTSTRAP='1',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(D/'target'))
cmd=['cargo','rustc','--manifest-path',str(P/'Cargo.toml'),'--release','--lib','-j','4','--','--emit=mir','-Zmir-opt-level=4'];(O/'command.json').write_text(json.dumps(dict(argv=cmd,toolchain=tc),indent=2));r=subprocess.run(cmd,env=env)
if not r.returncode:
 p=max((D/'target/release/deps').glob('pv_fscan_concrete-*.mir'),key=lambda p:p.stat().st_mtime);b=p.read_bytes();(O/'crate.mir').write_bytes(b);(O/'mir-identity.json').write_text(json.dumps(dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b))))
sys.exit(r.returncode)
