from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','wrong_after','wrong_byte','wrong_reply']
subprocess.run([sys.executable,str(E/'NEQ_prepare_result_window.py'),'8','positive'],check=True)
p=E/'NEQ_native_contracts.patch';s=p.read_text();head,rest=s.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_window.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'));body=body[:body.index('#[kani::proof]')]
body+='''
struct Tail<'a>{expected:&'a PoolV1PairForestTerminalResultV1,other:&'a PoolV1PairVerifiedAfterstateV1,reply:Result<[u8;688],PoolV1PairVerifierTransportErrorV1>,calls:u8,offset:usize}
fn child(a:&PoolV1PairVerifiedAfterstateV1,f:&mut Tail)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{assert!(f.calls==2&&core::ptr::eq(a,&f.expected.verified_afterstate));f.calls=3;REPLY}
fn tail(r:&PoolV1PairForestTerminalResultV1,output:&mut[u8;792],f:&mut Tail)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{let bytes=child(ARG,f).map_err(|e|PoolV1PairForestTerminalFormatErrorV1::Afterstate(e))?;let dst=&mut output[104..];let src=&bytes;let mut i=f.offset;dst[i]=src[i]CORRUPT;i+=1;assert!(i==f.offset+1);Ok(())}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn result_tail(){let r=result();let other=NEE_common().lane_transition.candidate_afterstate;let mut output:[u8;792]=kani::any();let j:usize=kani::any();kani::assume(j<792);let old=output[j];let offset:usize=kani::any();kani::assume(offset<688);let mut f=Tail{expected:&r,other:&other,reply:if kani::any(){Ok(kani::any())}else{Err(NEE_any_PoolV1PairVerifierTransportErrorV1())},calls:2,offset};let expected=f.reply.map(|_|()).map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate);let actual=tail(&r,&mut output,&mut f);assert!(actual==expected&&f.calls==3,"full afterstate Result and source suffix order");let wanted=if f.reply.is_ok()&&j==104+offset{match f.reply{Ok(bytes)=>bytes[offset],_=>0}}else{old};assert!(output[j]==wanted,"same full child reply and complete prestate frame");}
'''.replace('ARG','f.other' if mode=='wrong_after' else '&r.verified_afterstate').replace('CORRUPT','^1' if mode=='wrong_byte' else '').replace('REPLY','if f.reply.is_ok(){Err(PoolV1PairVerifierTransportErrorV1::WrongMagic)}else{Ok([0u8;688])}' if mode=='wrong_reply' else 'f.reply')
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_result_window.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines()))
(E/'NEQ_RESULT_TAIL_CURRENT.json').write_text(json.dumps(dict(mode=mode,all_typed_inputs=True,arbitrary_prestate=True,full_afterstate_Result=True,one_KMX_step=True,invariant='validator and digest prefix completed; calls=2; exact same result; output arbitrary; 0<=offset<688',classification='ruling y same returned688 reply/error and one suffix copy step; no root credit by itself'),indent=1)+'\n')
