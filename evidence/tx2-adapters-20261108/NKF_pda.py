from NKF_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
SITES=[
 ('registry_v2','&[VERIFIER_REGISTRY_V2_SEED,key0.as_ref(),&[bump]]','&program'),
 ('registry_programdata','&[key0.as_ref(),&[bump]]','&program'),
 ('entry_v2','&[VERIFIER_ENTRY_V2_SEED,key0.as_ref(),&PROFILE_BINDING,&RELEASE_BINDING,&[bump]]','&program'),
 ('verifier_programdata','&[key0.as_ref(),&[bump]]','&program'),
 ('registry_v1','&[VERIFIER_REGISTRY_SEED,key0.as_ref(),&[bump]]','&program'),
 ('entry_v1','&[VERIFIER_ENTRY_SEED,key0.as_ref(),&PROFILE_BINDING,&RELEASE_BINDING,&[bump]]','&program'),
 ('master','&[PAIR_FOREST_MASTER_SEED,key0.as_ref(),&[bump]]','&program'),
 ('checkpoint','&[PAIR_FOREST_CHECKPOINT_SEED,key0.as_ref(),&sequence.to_le_bytes(),&[bump]]','&program'),
 ('lane','&[PAIR_FOREST_LANE_SEED,key0.as_ref(),&[lane],&[bump]]','&program')]
COMMON='''use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use solana_program::pubkey::PubkeyError;
struct Log{count:usize,lens:[usize;5],bytes:[u8;5],program:u8,returned:bool,output:u8}
fn byte(s:&[u8],i:usize)->u8{if i<s.len(){s[i]}else{0}}
fn oracle(log:&mut Log,seeds:&[&[u8]],program:&Pubkey,reply:Result<Pubkey,PubkeyError>,i:usize)->Result<Pubkey,PubkeyError>{
 log.count=seeds.len();log.program=program.to_bytes()[i];
 if seeds.len()>0{log.lens[0]=seeds[0].len();log.bytes[0]=byte(seeds[0],i);}
 if seeds.len()>1{log.lens[1]=seeds[1].len();log.bytes[1]=byte(seeds[1],i);}
 if seeds.len()>2{log.lens[2]=seeds[2].len();log.bytes[2]=byte(seeds[2],i);}
 if seeds.len()>3{log.lens[3]=seeds[3].len();log.bytes[3]=byte(seeds[3],i);}
 if seeds.len()>4{log.lens[4]=seeds[4].len();log.bytes[4]=byte(seeds[4],i);}
 match &reply{Ok(key)=>{log.returned=true;log.output=key.to_bytes()[i];},Err(_)=>{log.returned=false;}}
 reply
}
fn any_reply()->Result<Pubkey,PubkeyError>{let tag:u8=kani::any();kani::assume(tag<4);match tag{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(PubkeyError::MaxSeedLengthExceeded),2=>Err(PubkeyError::InvalidSeeds),_=>Err(PubkeyError::IllegalOwner)}}
'''
def packet(which):
 name,seeds,program=SITES[which]
 call='oracle(&mut log,'+seeds+','+program+',reply,i)'
 # Oracle substitution is ONLY at the child call, not a SHA/curve model.
 text=COMMON+'''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage(){
 let key0=Pubkey::new_from_array(kani::any());let program=Pubkey::new_from_array(kani::any());let expected=Pubkey::new_from_array(kani::any());
 let bump:u8=kani::any();let sequence:u64=kani::any();let lane:u8=kani::any();let i:usize=kani::any();let slot:usize=kani::any();kani::assume(i<32&&slot<5);
 let reply=any_reply();let expected_ok=matches!(&reply,Ok(_));let reply_byte=match &reply{Ok(p)=>Some(p.to_bytes()[i]),Err(_)=>None};
 let mut log=Log{count:0,lens:[0;5],bytes:[0;5],program:0,returned:false,output:0};
 let result=(||->Result<Pubkey,ProgramError>{
  let found=CALL.map_err(|_|ProgramError::InvalidAccountData)?;
  Ok(found)
 })();
 let expected_seeds: &[&[u8]]=SEEDS;
 let expected_len=if slot<expected_seeds.len(){expected_seeds[slot].len()}else{0};
 let expected_byte=if slot<expected_seeds.len(){byte(expected_seeds[slot],i)}else{0};
 let status=if expected_ok{matches!(&result,Ok(_))}else{matches!(&result,Err(ProgramError::InvalidAccountData))};
 let returned_byte=match (&result,reply_byte){(Ok(p),Some(v))=>p.to_bytes()[i]==v,(Err(_),None)=>true,_=>false};
 let unchanged_reply=match reply_byte{Some(b)=>log.returned&&log.output==b,None=>!log.returned};
 let good=status&&log.count==expected_seeds.len()&&log.lens[slot]==expected_len&&log.bytes[slot]==expected_byte&&log.program==program.to_bytes()[i]&&unchanged_reply&&returned_byte;
 assert!(if cfg!(NKF_invert){!good}else{good},"PDA cut bytes reply and frame");
}
'''.replace('CALL',call).replace('SEEDS',seeds)
 patch='--- /dev/null\n+++ b/programs/r1-cost-probe/src/NKF_pda.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True))
 (E/('NKF_pda_'+name+'.patch')).write_text(patch)
 return text
if __name__=='__main__':
 import sys
 a,n,mode=sys.argv[1:];text=packet(int(n));submit(a,'r1_pool_adapter::owned::NKF_pda::stage',P,'NKF_pda',text,mode)
