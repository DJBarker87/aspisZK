"""Isolate the constant multiplier using P=2^31-1; native div/rem unchanged."""
import subprocess
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
s='''
#[kani::proof]
fn LPk_sparse_constant_reconstruction() {
 let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));
 let n=(rem<<32)|u64::from(limb);
 let q=n/u64::from(P);let r=n%u64::from(P);
 kani::assume(q<=u64::from(u32::MAX)); // K008
 kani::assume(r<u64::from(P)); // K009
 let product=q.wrapping_shl(31).wrapping_sub(q);
 assert_eq!(product.wrapping_add(r),n);
}
'''
subprocess.run(['ssh',H,'cat >> '+B+'/LPk_src/crates/aspis-r1-cost-probe/src/LPk_harness.rs'],input=s,text=True,check=True)
