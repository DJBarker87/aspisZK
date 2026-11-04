"""Frozen request projections: scalar prefix, same suffix borrow, header copies."""
from pathlib import Path
import subprocess,sys,json,difflib,hashlib,re
E=Path(__file__).resolve().parent;shape,mode=sys.argv[1:];assert mode in ['positive','negative']
assert shape in ['prefix','payment_carrier','profile','release','pool_program','postguard']
subprocess.run([sys.executable,str(E/'NEU_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);a=f.index('pub fn decode_pool_v1_pair_forest_terminal_request_v1(');z=f.index('\n}',a)+2;original=f[a:z]
if shape=='prefix':
 body=original[:original.index('    let public =')].replace('pub fn decode_pool_v1_pair_forest_terminal_request_v1(\n    bytes: &[u8],\n) -> Result<PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalFormatErrorV1>','fn prefix(length:usize,bytes:&[u8;8])->Result<PoolV1TransitionKind,PoolV1PairForestTerminalFormatErrorV1>').replace('bytes.len()','length')+'    Ok(kind)\n}\n'
 body=body.replace('fn prefix(length:usize,bytes:&[u8;8])','fn prefix(length:usize,bytes:&[u8;8],bad_magic:bool)').replace('bytes[..4] != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC','bad_magic')
 ref='''fn reference(length:usize,b:&[u8;8],bad_magic:bool)->Result<PoolV1TransitionKind,PoolV1PairForestTerminalFormatErrorV1>{if length!=320{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)}if bad_magic{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}if b[4]!=1{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)}let k=match b[5]{1=>PoolV1TransitionKind::PrivateTransfer,2=>PoolV1TransitionKind::Withdrawal,_=>return Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)};if b[6]!=1{return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)}if b[7]!=0{return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}Ok(k)}'''
 body+=ref+'\n#[kani::proof]\nfn request_slice(){let bytes:[u8;8]=kani::any();let length:usize=kani::any();let bad_magic:bool=kani::any();assert!(prefix(length,&bytes,bad_magic)==reference(length,&bytes,bad_magic));}\n'
 if mode=='negative':body=body.replace('transition_kind(bytes[5])','transition_kind(bytes[6])')
elif shape=='payment_carrier':
 expr='&bytes[REQUEST_PAYMENT_OFFSET..]'
 body='''fn carrier(bytes:&[u8;320],j:usize){let child=@EXPR@;assert!(child.len()==216);assert!(core::ptr::eq(child.as_ptr(),bytes[104..].as_ptr()));assert!(child[j]==bytes[104+j] @BAD@);}
#[kani::proof]
fn request_slice(){let bytes:[u8;320]=kani::any();let j:usize=kani::any();kani::assume(j<216);carrier(&bytes,j);}
'''.replace('@EXPR@',expr).replace('@BAD@','^1' if mode=='negative' else '')
elif shape in ['profile','release','pool_program']:
 key={'profile':('verifier_profile',8,40),'release':('verifier_release',40,72),'pool_program':('pool_program',72,104)}[shape];name,lo,hi=key
 block=original[original.index('    let request ='):original.index('    if request.verifier_profile')]
 expr=re.search(r'\b'+name+r': (.*?\?)[,\n]',block,re.S).group(1)
 body='fn window(bytes:&[u8;320])->Result<[u8;32],PoolV1PairForestTerminalFormatErrorV1>{Ok('+expr+')}\n'
 body+='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn request_slice(){let bytes:[u8;320]=kani::any();let j:usize=kani::any();kani::assume(j<32);let out=window(&bytes).unwrap();assert!(out[j]==bytes[@LO@+j] @BAD@);}
'''.replace('@LO@',str(lo)).replace('@BAD@','^1' if mode=='negative' else '')
else:
 native=original[original.index('    if request.verifier_profile'):].replace('    Ok(request)','    Ok(())')
 native='fn guard(profile_zero:bool,release_zero:bool,pool_zero:bool)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{\n'+native.replace('request.verifier_profile == [0u8; 32]','profile_zero').replace('request.verifier_release == [0u8; 32]','release_zero').replace('request.pool_program == [0u8; 32]','pool_zero')
 body=native+'''\n#[kani::proof]
fn request_slice(){let p:bool=kani::any();let r:bool=kani::any();let q:bool=kani::any();let actual=guard(p,r,q);let good=!(p||r||q);assert!(actual==if good{Ok(())}else{Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)});}
'''
 if mode=='negative':body=body.replace('|| pool_zero','&& pool_zero')
body='use super::*;\n'+body
changed=f+'\n#[cfg(kani)]\n#[path="NEU_request.rs"]\nmod NEU_request;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEU_request.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEU_native_contracts.patch').write_text(patch)
(E/'NEU_REQUEST_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,frozen_body=original,frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),native=body,classification='source projection only; Eq4 magic and Eq32 zero-comparisons are explicit arbitrary Boolean leaves after K008 timeout, NOT proved; scalar error/control, borrow and copy only; full parent OPEN',domain='all metadata lengths and first8 bytes' if shape=='prefix' else 'every typed 320-byte request array' if shape!='postguard' else 'every three 32-byte binding arrays'),indent=1)+'\n')
