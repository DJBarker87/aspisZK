from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NBU_more.rs.txt';s=p.read_text();attrs=s[s.index('#[kani::proof]'):s.index('fn NBU_validator_control')].replace('1881','34')
body='''let s=NBU_statement();
match &s {
PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>{assert!(core::ptr::eq(s.nullifier(),&public.nullifier));assert_eq!(s.transition_kind(),PoolV1TransitionKind::PrivateTransfer);let p=PoolV1PairForestTerminalPaymentV1::PrivateTransfer(*public);if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(q)=&p{assert!(core::ptr::eq(p.nullifier(),&q.nullifier));assert_eq!(p.transition_kind(),PoolV1TransitionKind::PrivateTransfer);}else{assert!(false);}},
PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>{assert!(core::ptr::eq(s.nullifier(),&public.nullifier));assert_eq!(s.transition_kind(),PoolV1TransitionKind::Withdrawal);let p=PoolV1PairForestTerminalPaymentV1::Withdrawal(*public);if let PoolV1PairForestTerminalPaymentV1::Withdrawal(q)=&p{assert!(core::ptr::eq(p.nullifier(),&q.nullifier));assert_eq!(p.transition_kind(),PoolV1TransitionKind::Withdrawal);}else{assert!(false);}}
}'''
for neg in ['', '_negative']:
 b=body.replace('assert!(core::ptr::eq(s.nullifier(),&public.nullifier))','assert!(!core::ptr::eq(s.nullifier(),&public.nullifier))') if neg else body
 s+='\n'+attrs+'fn NBU_projection'+neg+'(){'+b+'}\n'
p.write_text(s)
p=E/'NBU_decode.rs.txt';s=p.read_text();attrs=s[s.index('#[kani::proof]'):s.index('fn NBU_decode_children')].replace('1881','34')
s+='\n'+attrs+'''fn NBU_exact_reject(){let raw:[u8;33]=kani::any();let n:usize=kani::any();kani::assume(n<=33 && n!=32);assert_eq!(exact::<32>(&raw[..n]),Err(PoolV1PairVerifierTransportErrorV1::WrongLength));}\n'''
p.write_text(s)
