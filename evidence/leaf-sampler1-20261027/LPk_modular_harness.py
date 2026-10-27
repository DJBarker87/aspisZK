import subprocess
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
s='''
// Split K010: only the low-word identity. The independent passed gates
// K008/K009 supply these two assumptions; Lean supplies the no-wrap lift.
#[kani::proof]
fn LPk_wrapping_reconstruction() {
 let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));
 let n=(rem<<32)|u64::from(limb);
 let q=n/u64::from(P);let r=n%u64::from(P);
 kani::assume(q<=u64::from(u32::MAX));
 kani::assume(r<u64::from(P));
 assert_eq!(q.wrapping_mul(u64::from(P)).wrapping_add(r),n);
}
'''
subprocess.run(['ssh',H,'cat >> '+B+'/LPk_src/crates/aspis-r1-cost-probe/src/LPk_harness.rs'],input=s,text=True,check=True)
