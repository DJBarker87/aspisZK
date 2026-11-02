"""Exact frozen payment encoder rejection prefix, arbitrary full validator Result."""
from pathlib import Path
import sys,subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative';assert case in ['transfer','withdrawal']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/payment_relation.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
fn='encode_pool_v1_'+('private_transfer' if case=='transfer' else 'withdrawal')+'_public_v1';Ty='PoolV1'+('PrivateTransfer' if case=='transfer' else 'Withdrawal')+'PublicV1';valid=fn.replace('encode_','validate_',1)
a=f.index('pub fn '+fn+'(');z=f.index('\n}',a)+2;old=f[a:z];statement=valid+'(public)?;';assert statement in old
P=E.parent/'slice-s-compose2-20261029';patch=(P/'NEE_K052-NEE_oracle.patch').read_text();error=next(l[1:] for l in patch.splitlines() if l.startswith('+fn NEE_any_PoolV1PaymentStatementFormatError')).replace('NEE_any_PoolV1PaymentStatementFormatError','any_error')
construct='recipient_commitment:digest(),change_commitment:digest()' if case=='transfer' else 'amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()'
body='''use super::*;
struct Frame<'a>{expected:&'a TYPE,reply:Result<(),PoolV1PaymentStatementFormatError>,log:u8,reached:bool}
fn child(p:&TYPE,f:&mut Frame)->Result<(),PoolV1PaymentStatementFormatError>{assert!(core::ptr::eq(p,f.expected)&&f.log==0,"actual caller public and empty prestate log");f.log=1;REPLY}
fn prefix(public:&TYPE,f:&mut Frame)->Result<(),PoolV1PaymentStatementFormatError>{child(public,f)?;f.reached=true;Ok(())}
ERROR
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn payment_prefix(){let p=TYPE{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),CONSTRUCT};let mut f=Frame{expected:&p,reply:if kani::any(){Ok(())}else{Err(any_error())},log:0,reached:false};let actual=prefix(&p,&mut f);assert!(actual==f.reply && f.log==1 && f.reached==f.reply.is_ok(),"complete Result and short-circuit continuation");}
'''.replace('TYPE',Ty).replace('CONSTRUCT',construct).replace('ERROR',error).replace('REPLY','if f.reply.is_ok(){Err(PoolV1PaymentStatementFormatError::WrongLength)}else{Ok(())}' if negative else 'f.reply')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_payment_prefix.rs"]\nmod NEM_payment_prefix;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_payment_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_PAYMENT_PREFIX_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=p,frozen_body=old,frozen_body_sha256=hashlib.sha256(old.encode()).hexdigest(),exact_prefix=statement,child_domain='all typed publics; no acceptance restriction',frame='only local log and reached-continuation flag; no output is initialized on rejection',reply='full arbitrary Result<(),PaymentError> including every error variant',classification='native source prefix with explicit pure continuation cut; suffix windows separate'),indent=1)+'\n')
