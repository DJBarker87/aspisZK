from pathlib import Path
import subprocess
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
s='''
#[kani::proof] #[kani::unwind(10)]
fn LPk_byte_decode() {
 let block:[u8;32]=kani::any();
 let quotient:[u32;8]=core::array::from_fn(|i|u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap()));
 let i:usize=kani::any();kani::assume(i<8);
 let word=u32::from(block[4*i])|(u32::from(block[4*i+1])<<8)|
  (u32::from(block[4*i+2])<<16)|(u32::from(block[4*i+3])<<24);
 assert_eq!(quotient[i],word);
}
'''
subprocess.run(['ssh',H,'cat >> '+B+'/LPk_src/crates/aspis-r1-cost-probe/src/LPk_harness.rs'],input=s,text=True,check=True)
