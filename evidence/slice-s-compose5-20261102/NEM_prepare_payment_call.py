"""Native payment suffix: exact child/field plus one KMX write and frame."""
from pathlib import Path
import sys,subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;case,mode=sys.argv[1:];negative=mode=='negative'
assert case in ['transfer_recipient','transfer_change','withdrawal_amount','withdrawal_destination','withdrawal_change']
subprocess.run([sys.executable,str(E/'NEM_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/payment_relation.rs';f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
transfer=case.startswith('transfer');Ty='PoolV1'+('PrivateTransfer' if transfer else 'Withdrawal')+'PublicV1';field=case.split('_')[1]
field={'recipient':'recipient_commitment','change':'change_commitment','amount':'amount','destination':'destination_token_account'}[field]
start={'recipient_commitment':152,'change_commitment':184,'amount':148,'destination_token_account':152}[field];width=4 if field=='amount' else 32
construct='recipient_commitment:digest(),change_commitment:digest()' if transfer else 'amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()'
if field in ['recipient_commitment','change_commitment']:
 call='let reply=child(&p.'+field+',&p.'+('anchor_root' if negative else field)+',&mut f);let src=&reply;'
 expected='f.reply[offset]'
elif field=='amount':
 call='let reply=('+('p.amount^1' if negative else 'p.amount')+').to_le_bytes();let src=&reply;';expected='p.amount.to_le_bytes()[offset]'
else:
 call='let src=&p.'+('pool' if negative else field)+';';expected='p.destination_token_account[offset]'
body='''use super::*;
struct Frame{reply:[u8;WIDTH],called:bool}
fn child(v:&Digest,expected:&Digest,f:&mut Frame)->[u8;WIDTH]{assert!(!f.called && core::ptr::eq(v,expected),"actual payment child borrow");f.called=true;f.reply}
fn digest()->Digest{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
#[kani::proof]
fn payment_call(){let p=TYPE{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),CONSTRUCT};
 let mut output:[u8;216]=kani::any();let offset:usize=kani::any();kani::assume(offset<WIDTH);let j:usize=kani::any();kani::assume(j<216);let old=output[j];let mut f=Frame{reply:kani::any(),called:false};
 CALL
 let dst=&mut output[START..START+WIDTH];let mut i=offset;dst[i]=src[i];i+=1;
 assert!(i==offset+1 && output[j]==if j==START+offset{EXPECTED}else{old},"same payment source reply and complete prestate frame");
 CALLED
}
'''.replace('WIDTH',str(width)).replace('TYPE',Ty).replace('CONSTRUCT',construct).replace('START',str(start)).replace('CALL',call).replace('EXPECTED',expected).replace('CALLED','assert!(f.called);' if field.endswith('commitment') else '')
# Replace the distinct marker before CALL to avoid accidental substring capture.
body=body.replace(call+'ED','assert!(f.called);' if field.endswith('commitment') else '')
changed=f+'\n#[cfg(kani)]\n#[path="NEM_payment_call.rs"]\nmod NEM_payment_call;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+='--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEM_payment_call.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())
(E/'NEM_native_contracts.patch').write_text(patch)
(E/'NEM_PAYMENT_CALL_CURRENT.json').write_text(json.dumps(dict(case=case,negative=negative,source=p,field=field,start=start,width=width,all_typed_inputs=True,arbitrary_prestate=True,full_frame=True,one_KMX_iteration=True,actual_child_borrow=True,classification='same-call payment suffix field/byte association, disjoint source-ordered frame composition separate',source_sha256=hashlib.sha256(f.encode()).hexdigest()),indent=1)+'\n')
