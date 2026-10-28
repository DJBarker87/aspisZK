from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent;p='programs/r1-cost-probe/src/lib.rs';old=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
tail=r'''
#[cfg(kani)]
mod NBQ_error_control {
 use super::*;
 static mut CALLS:usize=0;
 // Formatted bytes are outside the 03:00 soundness observation.
 fn private_format(_args:core::fmt::Arguments<'_>)->String{String::new()}
 fn private_log(_s:&str){unsafe{CALLS+=1;}}
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(std::fmt::format,private_format)]
 #[kani::stub(solana_program::log::sol_log,private_log)]
 fn rejects(){
  let tag:u8=kani::any();kani::assume(tag<8);
  use aspis_r1_cost_probe::verifier::Error;
  let error=match tag{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation};
  unsafe{CALLS=0;}
  assert!(super::error(error)==ProgramError::InvalidInstructionData);
  unsafe{assert!(CALLS==1);}kani::cover!(tag==7);
 }
}
'''
(E/'NBQ_error.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+tail).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
