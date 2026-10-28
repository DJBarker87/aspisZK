from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NBN_more.rs.txt';old=p.read_text();assert 'fn NBN_encoder_control' not in old
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
src=subprocess.check_output(['git','show',rev+':'+path],text=True)
vs=re.findall(r'(\w+)(?:\((\w+)\))?\s*,',re.search(r'pub enum PoolV1PairForestTerminalFormatErrorV1\s*\{([^}]+)\}',src).group(1))
extra='fn NBN_any_format()->PoolV1PairForestTerminalFormatErrorV1 { match kani::any::<u8>() {'+','.join((str(i) if i<len(vs)-1 else '_')+'=>PoolV1PairForestTerminalFormatErrorV1::'+v+(f'(NBN_any_{ty}())' if ty else '') for i,(v,ty) in enumerate(vs))+'} }\n'
# Exact caller order and SAME typed child references. Data stores are separately
# covered by NBH_K029/NBK_K042 and source layout lemmas, and intentionally absent here.
extra+='''
fn NBN_encoder_cut<V,D,L,T,W>(statement:&PoolV1PairForestTerminalStatementV1,mut validate:V,mut digest:D,mut late:L,mut transfer:T,mut withdraw:W)->Result<(),PoolV1PairForestTerminalFormatErrorV1>
where V:FnMut(&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>,
D:FnMut(&Digest)->[u8;32],L:FnMut(&PoolV1PairLatePublicStatementV1,&mut [u8])->Result<(),PoolV1PairLatePublicStatementErrorV1>,
T:FnMut(&PoolV1PrivateTransferPublicV1)->Result<[u8;216],PoolV1PaymentStatementFormatError>,
W:FnMut(&PoolV1WithdrawalPublicV1)->Result<[u8;216],PoolV1PaymentStatementFormatError>{
 validate(statement)?;
 let common=statement.common();let mut output=[0u8;POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES];
 let _anchor=digest(&common.historical_global_anchor);
 late(&common.lane_transition,&mut output[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET]).map_err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition)?;
 let _payment=match statement {PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>transfer(public),PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>withdraw(public)}.map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?;
 Ok(())
}
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_encoder_control(){
 let s=NBN_statement();let stage=core::cell::Cell::new(0u8);let is_transfer=matches!(s,PoolV1PairForestTerminalStatementV1::PrivateTransfer{..});
 let v=if kani::any::<bool>() {Ok(())} else {Err(NBN_any_format())};
 let l=if kani::any::<bool>() {Ok(())} else {Err(NBN_any_PoolV1PairLatePublicStatementErrorV1())};
 let p=if kani::any::<bool>() {Ok([0;216])} else {Err(NBN_any_PoolV1PaymentStatementFormatError())};
 let actual=NBN_encoder_cut(&s,|x|{assert_eq!(stage.get(),0);assert!(core::ptr::eq(x,&s));stage.set(1);v},
 |d|{assert_eq!(stage.get(),1);assert!(core::ptr::eq(d,&s.common().historical_global_anchor));stage.set(2);[0;32]},
 |x,out|{assert_eq!(stage.get(),2);assert!(core::ptr::eq(x,&s.common().lane_transition));assert_eq!(out.len(),1520);stage.set(3);l},
 |x|{assert_eq!(stage.get(),3);assert!(is_transfer);if let PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=&s {assert!(core::ptr::eq(x,public));}else {assert!(false);}stage.set(4);p},
 |x|{assert_eq!(stage.get(),3);assert!(!is_transfer);if let PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=&s {assert!(core::ptr::eq(x,public));}else {assert!(false);}stage.set(4);p});
 let expected=match v {Err(e)=>Err(e),Ok(())=>match l {Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::LaneTransition(e)),Ok(())=>p.map(|_|()).map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)}};
 assert_eq!(actual,expected);assert_eq!(stage.get(),if v.is_err(){1}else if l.is_err(){3}else{4});
}
'''
p.write_text(old+extra)
(E/'NBN_ENCODER_EXTEND.json').write_text(json.dumps(dict(source=p.name,previous_sha256=hashlib.sha256(old.encode()).hexdigest(),frozen_revision=rev,source_path=path,native_cut='ordered callbacks on exact same typed refs; exact source data-store cuts inherited, no whole encoder claim from this gate alone',output_data_unobserved=True,unwind=1881),indent=2)+'\n')
