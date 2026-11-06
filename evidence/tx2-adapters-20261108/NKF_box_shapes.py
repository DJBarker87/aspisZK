from NKF_wrappers import *
def shape(kind,mode):
 typ=M if kind=='master' else C
 text=COMMON+'''
#[kani::ensures(|out| ENSURES)]
#[kani::modifies(MODIFIES)]
fn shape_probe(seed:u8,scratch:&mut u8)->Result<Box<TYPE>,ProgramError>{
 *scratch=seed;
 if seed&1==0{let mut value=ANY;value.bump=seed;Ok(Box::new(value))}else{Err(ProgramError::InvalidAccountData)}
}
fn check(seed:u8,out:Result<Box<TYPE>,ProgramError>){match out{Ok(p)=>assert!(p.bump==seed,"unimplied boxed bump"),Err(e)=>assert!(e==ProgramError::InvalidAccountData,"unimplied boxed error")}}
#[kani::proof_for_contract(shape_probe)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_contract(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}
#[kani::proof] #[kani::stub_verified(shape_probe)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_unimplied(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}
'''.replace('TYPE',typ).replace('ANY','any_'+kind+'()').replace('ENSURES','false' if mode=='inverse' else 'true').replace('MODIFIES','' if mode=='modifies' else 'scratch')
 return text
if __name__=='__main__':
 import sys
 a,kind,mode=sys.argv[1:];text=shape(kind,mode);target='shape_unimplied' if mode=='unimplied' else 'shape_contract'
 (E/('NKF_'+kind+'_shape_'+mode+'.patch')).write_text('--- /dev/null\n+++ b/NKF_'+kind+'_shape.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 submit(a,'r1_pool_adapter::NKF_'+kind+'_shape::'+target,P,'NKF_'+kind+'_shape',text,mode='shape_'+mode)
