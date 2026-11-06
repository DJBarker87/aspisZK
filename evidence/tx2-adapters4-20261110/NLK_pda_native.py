from NLK_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
def attempt(a,part,mode):
 source=json.loads((E/'NLK_PUBKEY_SOURCE.json').read_text());s=source['text']
 start=s.index('            let mut bytes = [0; 32];',s.index('    pub fn create_program_address('));end=s.index('\n        }',start)
 segment=s[start:end]
 body=segment.replace('crate::syscalls::sol_create_program_address','oracle').replace('SUCCESS =>','0 =>')
 common='use super::*;\nuse solana_program::pubkey::PubkeyError;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
 ann='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
 text=common+ann+'''fn stage(){
 let seed0:[u8;32]=kani::any();let seed1:[u8;32]=kani::any();let seed2:[u8;32]=kani::any();let seed3:[u8;32]=kani::any();let seed4:[u8;32]=kani::any();
 let raw_program:[u8;32]=kani::any();let program=Pubkey::new_from_array(raw_program);let program_id=&program;
 let count:usize=kani::any();let selected:usize=kani::any();let coordinate:usize=kani::any();
 kani::assume(count>=2&&count<=5&&selected<count&&coordinate<32);
 let lengths:[usize;5]=kani::any();for j in 0..5 {kani::assume(lengths[j]<=32);}
 kani::assume(coordinate<lengths[selected]);
 let full:[&[u8];5]=[&seed0[..lengths[0]],&seed1[..lengths[1]],&seed2[..lengths[2]],&seed3[..lengths[3]],&seed4[..lengths[4]]];let seeds=&full[..count];
 let reply:[u8;32]=kani::any();let status:u64=kani::any();kani::assume(status<=2);
 let observer:usize=kani::any();kani::assume(observer<32);
 let mut calls=0u8;let mut seed_byte=0u8;let mut program_byte=0u8;let mut seed_count=0u64;let mut seed_len=0usize;
 let mut oracle=|seed_ptr:*const u8,n:u64,program_ptr:*const u8,out:*mut u8|->u64 {
  calls+=1;seed_count=n;
  unsafe {
   let descriptors=core::slice::from_raw_parts(seed_ptr as *const &[u8],n as usize);
   seed_len=descriptors[selected].len();seed_byte=descriptors[selected][coordinate];
   program_byte=*program_ptr.add(observer);
   for j in 0..32 {*out.add(j)=reply[j];}
  } status
 };
 let mut out=(||->Result<Pubkey,PubkeyError>{ BODY })(); CORRUPT
 let value_ok=match out {Ok(key)=>status==0&&key.to_bytes()[observer]==reply[observer],Err(e)=>status!=0&&e==PubkeyError::from(status)};
 assert!(PROPERTY,"deployed PDA syscall ordered descriptors program output status frame");
}
'''.replace('BODY',body)
 props={'frame':'calls==1&&frame[observer]==frame_before&&program.to_bytes()[observer]==raw_program[observer]', 'seeds':'calls==1&&seed_count==count as u64&&seed_len==lengths[selected]&&seed_byte==full[selected][coordinate]', 'program':'calls==1&&program_byte==raw_program[observer]', 'reply':'calls==1&&value_ok'}
 corrupt={'frame':'frame[observer]^=1;', 'seeds':'seed_byte^=1;', 'program':'program_byte^=1;', 'reply':'out=Err(PubkeyError::MaxSeedLengthExceeded);'}
 if part=='frame':text=text.replace('let mut out=(||','let mut frame:[u8;32]=kani::any();let frame_before=frame[observer];let mut out=(||')
 text=text.replace('PROPERTY',props[part]).replace('CORRUPT',corrupt[part] if mode=='inverse' else '')
 mod='NLK_pda'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=source['path'],source_sha256=source['sha256'],segment=segment,part=part,mode=mode,transcription='literal deployed branch; sole syscall replaced by local reply oracle; SUCCESS renamed to numeric0',domain='2..5 seeds, each length0..32; arbitrary seed/program/reply bytes; status0..2; selected nonempty byte',modifies='local log and exactly syscall output32',limits='unsupported-status abort separately required; local segment, no parent closure'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
