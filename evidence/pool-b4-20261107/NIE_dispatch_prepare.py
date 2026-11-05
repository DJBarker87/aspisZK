from pathlib import Path
import sys,re,json,hashlib
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs
from NIE_frozen_identity import frozen

def prepare(negative):
 path='programs/aspis-pool/src/processor.rs';text=frozen()[path].decode();start=text.index('pub fn process_instruction(');brace=text.index('{',start);end=brace+1;depth=1
 while depth:
  if text[end]=='{':depth+=1
  elif text[end]=='}':depth-=1
  end+=1
 body=text[brace+1:end-1];cut=body.index('    let magic =');region=body[cut:]
 magics=list(dict.fromkeys(re.findall(r'magic == (b"[^"]+"|[A-Z][A-Z0-9_]+)',region)))
 assert len(magics)>=8 and region.count('program::set_return_data(&[]);')==1
 transformed=region.replace('program::set_return_data(&[]);','NIE_clear(&[],log);')
 after='fn NIE_after_guard(program_id:&Pubkey,accounts:&[AccountInfo<\'_>],instruction_data:&[u8],log:&mut ClearLog)->ProgramResult {\n'+transformed+'\n}\n'
 src='''use super::*;
struct ClearLog {calls:usize}
fn NIE_clear(bytes:&[u8],log:&mut ClearLog) {assert!(bytes.is_empty());log.calls+=INCREMENT;}
BODY
ATTR
#[kani::proof]
#[kani::unwind(33)]
fn association() {
 let data:[u8;8]=kani::any();let len:usize=kani::any();kani::assume(len<=8);
 if len>=4 {let magic=&data[..4];kani::assume(!(EXCLUSIONS));}
 let program=Pubkey::new_from_array(kani::any());let mut log=ClearLog{calls:0};
 let result=NIE_after_guard(&program,&[],&data[..len],&mut log);
 assert!(result==Err(ProgramError::InvalidInstructionData));
 assert!(log.calls==usize::from(len>=4));
}
'''.replace('INCREMENT','2' if negative else '1').replace('BODY',after).replace('ATTR',attrs()).replace('EXCLUSIONS',' || '.join('magic == '+m for m in magics))
 origin=dict(path=path,caller='process_instruction',frozen_region_sha256=hashlib.sha256(region.encode()).hexdigest(),region_start_line=text[:brace+1].count('\n')+1+body[:cut].count('\n'),region_end_line=text[:end-1].count('\n')+1,only_changes=['region outlined after the entry clear/height guard','explicit local ClearLog parameter','one empty set_return_data call replaced by local empty-packet recorder'],excluded_magics=magics,source_erasure='Exact region string regenerated from frozen Git blob; inverse recorder replacement equals frozen region byte-for-byte')
 (E/'NIE_DISPATCH_ORIGIN.json').write_text(json.dumps(origin,indent=2)+'\n')
 stage(path,src,'source-exact post-entry-guard discriminator rejection and empty return-data-clear log','negative' if negative else 'positive','Every0..8-byte physical instruction slice with none of the frozen dispatcher magics when len>=4; arbitrary program key; no accounts/child is accessed on this rejected cut.','Arbitrary full production input/entry-height syscall, all recognized dispatch arms and physical request ownership remain OPEN. RuntimeReturnDataClear is retained; initial clear/height guard intentionally outside this exact staged interval.',dict(control='corrupt empty-clear call count' if negative else None,origin='NIE_DISPATCH_ORIGIN.json'))
