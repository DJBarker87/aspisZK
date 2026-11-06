from NKY_native import *
import ast
commonfile=subprocess.check_output(['git','show','HEAD:evidence/tx2-adapters-20261108/NKF_wrappers.py'],text=True)
COMMON=next(ast.literal_eval(n.value) for n in ast.parse(commonfile).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name)and t.id=='COMMON'for t in n.targets))
def run(a,kind,mode):
 typ='PoolV1PairForest'+kind.title()+'V1';child='decode_pool_v1_pair_forest_'+kind+'_v1';name='decode_'+kind+'_box';mod='NKY_'+kind+'_ownership'
 frozen=subprocess.check_output(['git','show','HEAD:evidence/tx2-adapters-20261108/NKF_'+kind+'_SOURCE.json'],text=True);frozen=json.loads(frozen)['frozen_body']
 corrupt='if let Ok(ref mut b)=out { **b = { let mut v=**b;v.bump^=1;v }; }' if mode=='value' else ''
 different='if let Ok(ref mut b)=out { let second=Box::new(**b); **b=**b;out=Ok(second); }' if mode=='allocation' else ''
 instrumented=f'''fn {name}(bytes: &[u8]) -> Result<Box<{typ}>, ProgramError> {{
    let raw={child}(bytes);
    let mut allocated: *const {typ}=core::ptr::null();
    let mut out=(|| {{let b=Box::new(raw.map_err(|_| ProgramError::InvalidAccountData)?);allocated=&*b;Ok(b)}})();
    {corrupt}
    {different}
    match (&raw,&out) {{
     (Ok(a),Ok(b))=>{{ assert!(core::ptr::eq(&**b,allocated),"same Box allocation");assert!(!core::ptr::eq(&**b,a),"fresh owned carrier");assert!(a.bump==b.bump,"unchanged allocation payload"); }},
     (Err(_),Err(e))=>{{assert!(*e==ProgramError::InvalidAccountData,"mapped error");assert!(allocated.is_null(),"no allocation on decoder error");}},
     _=>assert!(false,"same Result arm")
    }}
    out
}}'''
 text=COMMON+f'''
fn raw_oracle(_bytes:&[u8])->Result<{typ},F>{{if kani::any(){{Ok(any_{kind}())}}else{{Err(any_error())}}}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(aspis_statement::pool_v1::{child},raw_oracle)]
fn returned(){{let bytes:[u8;1]=kani::any();let _={name}(&bytes);}}
'''
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(kind=kind,mode=mode,edits=[[frozen,instrumented]],same_raw_call=True,allocation='Box::new at the original success continuation',domain='all typed raw Results; caller bytes unchanged, tail independent of byte length'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::'+mod+'::returned','programs/r1-cost-probe/src/r1_pool_adapter.rs',mod,text,mode,edits=[(frozen,instrumented)])
if __name__=='__main__':
 import sys
 run(*sys.argv[1:])
