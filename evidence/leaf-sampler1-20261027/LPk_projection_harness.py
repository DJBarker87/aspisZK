"""Split the timed-out wrapping equality into four disjoint 16-bit goals."""
import subprocess
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
s='''
fn LPk_reconstruction_words()->(u64,u64) {
 let rem:u64=kani::any();let limb:u32=kani::any();kani::assume(rem<u64::from(P));
 let n=(rem<<32)|u64::from(limb);
 let q=n/u64::from(P);let r=n%u64::from(P);
 kani::assume(q<=u64::from(u32::MAX)); // K008
 kani::assume(r<u64::from(P)); // K009
 (q.wrapping_mul(u64::from(P)).wrapping_add(r),n)
}
'''
for i in range(4):
 s+=f'''#[kani::proof]
fn LPk_reconstruction_chunk{i}() {{
 let(w,n)=LPk_reconstruction_words();
 assert_eq!((w>>{16*i}) as u16,(n>>{16*i}) as u16);
}}
'''
subprocess.run(['ssh',H,'cat >> '+B+'/LPk_src/crates/aspis-r1-cost-probe/src/LPk_harness.rs'],input=s,text=True,check=True)
