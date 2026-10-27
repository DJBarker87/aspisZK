from pathlib import Path
import difflib,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-extract-20261027'
leaf='''//! Candidate host-prover-only extraction leaf. See design/PV-EXTRACT-20261027.md.
use aspis_core::field::{CM31, M31, QM31};

pub(crate) fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = QM31::from_cm31(CM31::from_m31(tag));
    let mut power = lambda;
    let mut i = 0usize;
    while i < values.len() {
        compressed = compressed.add(power.mul_m31(values[i]));
        power = power.mul(lambda);
        i = i.wrapping_add(1);
    }
    compressed
}
'''
changes=[]
def change(path,old,new):
 changes.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
path='crates/aspis-r1-cost-probe/src/prover_shared.rs';change(path,'',leaf)
path='crates/aspis-r1-cost-probe/src/lib.rs';s=(R/path).read_text();change(path,s,s+'\n#[cfg(all(feature = "prover", feature = "r1p-check"))]\nmod prover_shared;\n')
path='crates/aspis-r1-cost-probe/src/host_semantic.rs';s=(R/path).read_text();old='aspis_statement::compress_tagged_tuple(tag,&limbs,lambda)';assert s.count(old)==1;change(path,s,s.replace(old,'crate::prover_shared::compress_tagged_tuple(tag,&limbs,lambda)'))
(E/'route-ii-op223.patch').write_text(''.join(changes))
# Transport a standalone extraction probe only. Never apply the patch to crates/.
D='/home/dombarker/project-offloads/codex-pv-extract-20261027';subprocess.run(['ssh','dombarker@100.108.41.90','mkdir -p '+D+'/index-probe'],check=True)
cargo='''[package]
name = "pv-ext-index-probe"
version = "0.0.0"
edition = "2021"
[workspace]
[lib]
path = "lib.rs"
[dependencies]
aspis-core = { path = "../source/crates/aspis-core", features = ["r0", "ct-host-prover"] }
[profile.release]
opt-level = 3
overflow-checks = false
'''
for name,s in [('lib.rs',leaf.replace('pub(crate) fn','pub fn')),('Cargo.toml',cargo)]:
 subprocess.run(['ssh','dombarker@100.108.41.90','cat > '+D+'/index-probe/'+name],input=s,text=True,check=True)
