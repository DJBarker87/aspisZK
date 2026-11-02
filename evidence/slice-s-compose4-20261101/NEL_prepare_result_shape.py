from pathlib import Path
import subprocess,difflib,sys,json
E=Path(__file__).resolve().parent;shape,mode=sys.argv[1:];assert shape in ['unit_payment','u8_account'];assert mode in ['native','contract','unimplied','inverted','frame']
subprocess.run([sys.executable,str(E/'NEL_prepare_window.py'),'1','positive'],check=True)
path='crates/aspis-statement/src/pool_v1/payment_relation.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
Etype='PoolV1PaymentStatementFormatError' if shape=='unit_payment' else 'crate::pool_v1::PoolV1PairForestAccountErrorV1';T='()' if shape=='unit_payment' else 'u8';value='()' if shape=='unit_payment' else '17u8'
expr=f'*r==if b{{Ok({value})}}else{{Err({Etype}::NonCanonicalDigest)}}'
if mode=='inverted':expr='!('+expr+')'
frame='&mut f.y' if mode=='frame' else 'f'
body=f'''use super::*;
#[derive(kani::Arbitrary)]
struct State{{x:usize,y:usize}}
#[kani::modifies({frame})]
#[kani::ensures(|r| {expr})]
fn weak(f:&mut State,b:bool)->Result<{T},{Etype}>{{f.x=42;if b{{Ok({value})}}else{{Err({Etype}::NonCanonicalDigest)}}}}
'''
if shape=='u8_account':
 text=(E.parent/'slice-s-compose2-20261029/NEE_K052-NEE_oracle.patch').read_text()
 for name in ['PoolV1TreeError','PoolV1PairForestAccountErrorV1']:
  line=next(l[1:] for l in text.splitlines() if l.startswith('+fn NEE_any_'+name+'(')).replace('NEE_any_','any_')
  body+=line+'\n'
 body+='impl kani::Arbitrary for crate::pool_v1::PoolV1PairForestAccountErrorV1 {fn any()->Self{any_PoolV1PairForestAccountErrorV1()}}\n'
if mode in ['contract','inverted','frame']:
 body+='''#[kani::proof_for_contract(weak)]
fn shape_control(){let mut f=State{x:kani::any(),y:kani::any()};let _=weak(&mut f,kani::any());}
'''
else:
 body+='''#[kani::proof_for_contract(weak)]
fn support(){let mut f=State{x:kani::any(),y:kani::any()};let _=weak(&mut f,kani::any());}
#[kani::proof]
'''+('#[kani::stub_verified(weak)]\n' if mode=='unimplied' else '')+'''fn shape_control(){let mut f=State{x:kani::any(),y:kani::any()};let old=f.y;let _=weak(&mut f,kani::any());assert!(f.y==old,"unimplied external frame");}
'''
changed=frozen+'\n#[cfg(kani)]\n#[path="NEL_result_shape.rs"]\nmod NEL_result_shape;\n'
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEL_result_shape.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEL_native_contracts.patch').write_text(patch)
(E/'NEL_RESULT_SHAPE_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,return_type=f'Result<{T},{Etype}>',mutable_record=True,no_writable_static=True,credit='fidelity controls only; no frozen function closed'),indent=1)+'\n')
