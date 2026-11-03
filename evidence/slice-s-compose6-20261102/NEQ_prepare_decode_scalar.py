from pathlib import Path
import subprocess,sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];assert case in ['header','m31','digest'] and mode in ['positive','value','guard']
subprocess.run([sys.executable,str(E/'NEQ_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/payment_relation.rs' if case=='header' else 'crates/aspis-statement/src/atomic_statement.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
if case=='header':
 body='''use super::*;
fn reference(b:&[u8;216],m:[u8;4],k:PoolV1TransitionKind)->Result<(),PoolV1PaymentStatementFormatError>{if b[0]!=m[0]||b[1]!=m[1]||b[2]!=m[2]||b[3]!=m[3]{Err(PoolV1PaymentStatementFormatError::WrongMagic)}else if b[4]!=POOL_V1_PAYMENT_STATEMENT_VERSION{Err(PoolV1PaymentStatementFormatError::WrongVersion)}else if b[5]!=k as u8{Err(PoolV1PaymentStatementFormatError::WrongTransitionKind)}else if b[6]!=POOL_V1_DIGEST_ENCODING_VERSION{Err(PoolV1PaymentStatementFormatError::WrongDigestEncoding)}else if b[7]!=0{Err(PoolV1PaymentStatementFormatError::NonZeroReserved)}else{Ok(())}}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn decode_scalar(){let bytes:[u8;216]=kani::any();let magic:[u8;4]=kani::any();let kind=if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};let actual=require_header(&bytes,MAGIC,kind);let expected=reference(&bytes,magic,kind);assert!(actual==EXPECTED,"complete header Result, all guards, both variants and arbitrary magic");}
'''.replace('MAGIC','[magic[0]^1,magic[1],magic[2],magic[3]]' if mode=='guard' else 'magic').replace('EXPECTED','if expected.is_ok(){Err(PoolV1PaymentStatementFormatError::WrongMagic)}else{expected}' if mode=='value' else 'expected');fn='require_header'
elif case=='m31':
 body='''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn decode_scalar(){let bytes:[u8;4]=kani::any();let word=u32::from_le_bytes(bytes);let actual=M31::from_le_bytes(bytes).map(|x|x.0);let expected=if word COMPARE 2147483647{None}else{Some(word VALUE)};assert!(actual==expected,"full Option raw-word parser and exact accepted value");}
'''.replace('COMPARE','>' if mode=='guard' else '>=').replace('VALUE','^1' if mode=='value' else '');fn='M31::from_le_bytes'
else:
 words=','.join('u32::from_le_bytes([bytes['+str(4*i)+'],bytes['+str(4*i+1)+'],bytes['+str(4*i+2)+'],bytes['+str(4*i+3)+']])' for i in range(8))
 guard='||'.join('w['+str(i)+']'+('>' if mode=='guard' else '>=')+'2147483647' for i in range(8))
 body='''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn decode_scalar(){let bytes:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<8);let w:[u32;8]=[WORDS];let actual=decode_digest_canonical(&bytes);let expected=if GUARD{Err(AtomicStatementError::NonCanonicalDigest)}else{Ok(w)};match(actual,expected){(Ok(d),Ok(w))=>assert!(d[j].0==w[j]VALUE,"every same accepted limb"),(Err(e),Err(w))=>assert!(e==w,"same exact rejection"),_=>assert!(false,"same complete Result variant")}}
'''.replace('WORDS',words).replace('GUARD',guard).replace('VALUE','^1' if mode=='value' else '');fn='decode_digest_canonical'
module='NEQ_decode_scalar';changed=f+'\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n';patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));folder=p.rsplit('/',1)[0]
patch+='--- /dev/null\n+++ b/'+folder+'/'+module+'.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NEQ_native_contracts.patch').write_text(patch)
(E/'NEQ_DECODE_SCALAR_CURRENT.json').write_text(json.dumps(dict(case=case,mode=mode,function=fn,all_typed_inputs=True,all_return_variants=True,arbitrary_observed_limb=case=='digest',classification='actual frozen pure scalar/header/unrolled8 parser; no field multiplication, protocol loop, static, or native child stub'),indent=1)+'\n')
