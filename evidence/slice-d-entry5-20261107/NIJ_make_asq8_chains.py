from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NIJ_NATIVE_INPUTS.json').read_text());p='programs/r1-cost-probe/src/NIJ_auth.rs';s=x[p]
for stage in ['master','checkpoint','lane']:
 for suf,bad in [('',False),('_wrong',True)]:
  n='asq8_'+stage+suf
  s+=f'''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{
 let first:bool=kani::any();let second:bool=kani::any();let tag:u8=kani::any();kani::assume(tag<4);
 let expected=Pubkey::new_from_array(kani::any());let returned=Pubkey::new_from_array(kani::any());
 use solana_program::pubkey::PubkeyError::*;
 let reply=match tag{{0=>Ok(returned),1=>Err(MaxSeedLengthExceeded),2=>Err(InvalidSeeds),_=>Err(IllegalOwner)}};
 let mut pda_calls=0u8;let mut observed_tag=255u8;
 let result=(||->ProgramResult{{
  if first || second || {{pda_calls+=1;observed_tag=tag;reply.map_err(|_|ProgramError::InvalidAccountData)? != expected}}
  {{return Err(ProgramError::InvalidAccountData);}}
  Ok(())
 }})();
 let expected_calls=if first||second{{0}}else{{1}};
 let expected_ok=!first&&!second&&tag==0&&returned==expected;
 let good=pda_calls==expected_calls&&observed_tag==if expected_calls==0{{255}}else{{tag}}
  &&if expected_ok{{matches!(result,Ok(()))}}else{{matches!(result,Err(ProgramError::InvalidAccountData))}};
 assert!({'!' if bad else ''}good);
}}
'''
x[p]=s;(E/'NIJ_NATIVE_INPUTS.json').write_text(json.dumps(x));(E/'NIJ_auth.rs.txt').write_text(s);pins=json.loads((E/'NIJ_SOURCE_PINS.json').read_text());pins[p]=hashlib.sha256(s.encode()).hexdigest();(E/'NIJ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1))
(E/'NIJ_ASQ8_CHAINS.json').write_text(json.dumps(dict(stages=['master','checkpoint','lane'],scope='After the two actual scalar/key comparison operands, before actual PDA: native short-circuit/Result propagation/SAME returned-key comparison. First/second are arbitrary stage pre-state values, no success restriction. Seed/program arguments reuse nine NHY PDA packets by SHA; complete typed decoded-record/projection joins still required.',errors=['MaxSeedLengthExceeded','InvalidSeeds','IllegalOwner'],copy='Exact KMX patch, matched negative per source stage',credit='support only, authentication roots not CLOSED'),indent=1))
