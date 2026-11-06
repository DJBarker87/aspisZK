from NKY_box_native import *
def frame_run(a,kind,mode):
 typ='PoolV1PairForest'+kind.title()+'V1';child='decode_pool_v1_pair_forest_'+kind+'_v1';mod='NKY_'+kind+'_frame'
 fieldfile=(E.parent/'tx2-adapters2-20261108/NKP_box_tail.py').read_text()
 fields=next(ast.literal_eval(n.value) for n in ast.parse(fieldfile).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name)and t.id=='FIELDS'for t in n.targets))[kind]
 lefts=[v.split('==')[0].replace('a.','value.') for v in fields]
 observer='fn observed(value:&'+typ+',tag:usize,j:usize)->u64 {match tag {'+','.join(str(i)+'=>('+v+') as u64'for i,v in enumerate(lefts))+',_=>0}}'
 mutation=[]
 for i,v in enumerate(lefts):
  lhs=v.replace('value.','guard.')
  mutation.append(str(i)+'=>{'+(lhs+' = !'+lhs+';' if v.endswith('has_checkpoint') else lhs+' ^= 1;')+'}')
 mutant='match tag {'+','.join(mutation)+',_=>{}}' if mode=='frame' else '' 
 if mode=='alias':
  asserts='kani::assume(out.is_ok());out=Ok(guard);if let Ok(b)=out {assert!(!core::ptr::eq(&*b,pointer),"new allocation disjoint from live heap");}'
 else:
  asserts=f'''{mutant}
  assert!(observed(&guard,tag,j)==snapshot,"full pre-existing allocation frame");
  if let Ok(b)=out {{assert!(!core::ptr::eq(&*b,pointer),"new allocation disjoint from live heap");}}
'''
 text=COMMON+observer+f'''
fn raw_oracle(_bytes:&[u8])->Result<{typ},F>{{if kani::any(){{Ok(any_{kind}())}}else{{Err(any_error())}}}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(aspis_statement::pool_v1::{child},raw_oracle)]
fn returned(){{
 let tag:usize=kani::any();kani::assume(tag<{len(fields)});let j:usize=kani::any();kani::assume(j<32);
 let mut guard=Box::new(any_{kind}());let snapshot=observed(&guard,tag,j);let pointer=&*guard as *const {typ};
 let bytes:[u8;1]=kani::any();let mut out=decode_{kind}_box(&bytes);
 {asserts}
}}
'''
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::returned','programs/r1-cost-probe/src/r1_pool_adapter.rs',mod,text,mode)
if __name__=='__main__':
 import sys
 frame_run(*sys.argv[1:])
