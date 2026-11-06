from NKF_wrappers import *
def ownership(kind,mode):
 typ=M if kind=='master' else C
 rawfn='any_'+kind+'()'
 code=COMMON+'''
#[kani::requires(log.is_none())]
#[kani::modifies(log)]
#[kani::ensures(|out| match out {Ok(b)=>*log==Some((&**b as *const TYPE)as usize),Err(_)=>log.is_none()})]
fn allocation(raw:Result<TYPE,F>,log:&mut Option<usize>)->Result<Box<TYPE>,ProgramError>{
 let value=raw.map_err(|_|ProgramError::InvalidAccountData)?;
 let boxed=Box::new(value);
 *log=Some((&*boxed as *const TYPE)as usize);
 RETURN
}
#[kani::proof_for_contract(allocation)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation_identity(){let mut log=None;let raw=if kani::any(){Ok(ANY)}else{Err(any_error())};let _=allocation(raw,&mut log);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn allocation_unique(){let value=ANY;let sentinel=Box::new(ANY);let address=(&*sentinel as *const TYPE)as usize;let mut log=None;let out=allocation(Ok(value),&mut log).unwrap();let good=(&*out as *const TYPE)as usize!=address;assert!(UNIQUE);let _=sentinel;}
'''.replace('TYPE',typ).replace('ANY',rawfn).replace('UNIQUE','!good' if mode=='inverse_unique' else 'good')
 ret='let other=Box::new(value);drop(boxed);Ok(other)' if mode=='different_allocation' else 'Ok(boxed)'
 return code.replace('RETURN',ret)
if __name__=='__main__':
 import sys
 a,kind,mode=sys.argv[1:];name='allocation_unique' if 'unique' in mode else 'allocation_identity';text=ownership(kind,mode)
 (E/('NKF_'+kind+'_'+mode+'.patch')).write_text('--- /dev/null\n+++ b/NKF_'+kind+'_allocation.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 submit(a,'r1_pool_adapter::NKF_'+kind+'_allocation::'+name,P,'NKF_'+kind+'_allocation',text,mode)
