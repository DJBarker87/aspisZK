from pathlib import Path
E=Path(__file__).resolve().parent
s=''.join(l[1:] for l in (E.parent/'slice-d-entry6-20261107/NIS_forward.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
setup=s[s.index(' let p=Pubkey'):s.index(' let result=')]
setup=setup[:setup.index(' let first=')]+''' let data=if SECOND{&[65,83,81,56][..]}else{&[3,10][..]};
'''
setup=setup.replace('let a=core::mem::ManuallyDrop::new([','let mut a=core::mem::ManuallyDrop::new([')
setup=setup.replace(' let count=if SECOND', ''.join(' {let pick:usize=kani::any();kani::assume(pick<='+str(i)+');if pick<'+str(i)+'{a['+str(i)+']=a[pick].clone();}}\n' for i in range(1,7))+' let count=if SECOND')
t='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn field(a:&OwnedAccount,f:u32)->u8{match f{0..=31=>a.key.to_bytes()[f as usize],32..=63=>a.owner.to_bytes()[(f-32)as usize],64=>a.is_signer as u8,65=>a.is_writable as u8,66=>a.executable as u8,67..=74=>match a.length{Ok(n)=>((n>>((f-67)*8))&255)as u8,_=>{assert!(false,"snapshot length exact returning SDK arm");0}},_=>{assert!(matches!(a.bytes,Err(ProgramError::InvalidAccountData)),"deferred malformed length error exact");1}}}
fn logged(a:&[OwnedAccount],port:usize)->ProgramError{let f:u32=kani::any();kani::assume(f<76);ProgramError::Custom((f<<8)|field(&a[port],f)as u32)}
fn clear(d: &[u8]){assert!(d.is_empty(),"same empty return-data clear argument");}
fn clock()->Result<Clock,ProgramError>{Ok(Clock{slot:kani::any(),epoch_start_timestamp:kani::any(),epoch:kani::any(),leader_schedule_epoch:kani::any(),unix_timestamp:kani::any()})}
fn check<const SECOND:bool,const PORT:usize>(wrong:bool){
'''+setup+''' let before_lamps=lamps;
 let result=if SECOND{stage2(&p,accounts,data)}else{stage1(&p,accounts,data)};
 match result{Err(ProgramError::Custom(code))=>{let f=code>>8;assert!(f<76);let a=&accounts[PORT];let expected=match f{0..=31=>a.key.to_bytes()[f as usize],32..=63=>a.owner.to_bytes()[(f-32)as usize],64=>a.is_signer as u8,65=>a.is_writable as u8,66=>a.executable as u8,67=>1,68..=74=>0,_=>1};assert!(((code&255)==expected as u32)!=wrong,"same snapshot produced metadata,length,error at actual child");},_=>assert!(false,"logged error forwarded")}
 // No account data or lamport payload write occurs on this child-Err branch.
 assert!(lamps==before_lamps);
}
'''
# Lamps cannot be accessed while mutably borrowed by AccountInfo: record before creation.
t=t.replace(' let before_lamps=lamps;','').replace(' let mut lamps:[u64;7]=kani::any();',' let mut lamps:[u64;7]=kani::any();let before_lamps=lamps;')
for second,n in [(False,3),(True,7)]:
 for i in range(n):
  name=('second' if second else 'first')+str(i)
  sig='(_: &Pubkey,a:&[OwnedAccount],_:&[u8]'+',_:Result<u64,ProgramError>'*second+')'
  result='ProgramResult' if second else 'Result<Vec<u8>,ProgramError>'
  t+='fn '+name+'_log'+sig+'->'+result+'{Err(logged(a,'+str(i)+'))}\n'
  for neg in [False,True]:
   t+='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
   t+='#[kani::stub(super::stage'+('2' if second else '1')+'_owned,'+name+'_log)]\n'
   if second:t+='#[kani::stub(solana_program::program::set_return_data,clear)]\n#[kani::stub(Clock::get,clock)]\n'
   t+='fn '+name+('_wrong' if neg else '')+'(){check::<'+str(second).lower()+','+str(i)+'>('+str(neg).lower()+');}\n'
p='programs/r1-cost-probe/src/NIV_sdk.rs';(E/'NIV_sdk.patch').write_text('--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(t.splitlines()))+' @@\n'+''.join('+'+l for l in t.splitlines(True)))
