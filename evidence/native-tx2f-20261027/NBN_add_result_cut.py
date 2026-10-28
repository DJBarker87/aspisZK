from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NBN_more.rs.txt';old=p.read_text();assert 'fn NBN_result_control' not in old
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
a=src.index('fn validate_result(');b=src.index('\npub fn ',a)
body=src[a:b].split('\n///')[0]
# b reaches next public function; trim exact closing function before doc comments.
end=body.index('\n}\n')+3;body=body[:end]
body=body.replace('fn validate_result(','fn NBN_result_cut<L,A>(').replace('    result: &PoolV1PairForestTerminalResultV1,','    result: &PoolV1PairForestTerminalResultV1, mut lane:L, mut after:A,').replace(') -> Result<(), PoolV1PairForestTerminalFormatErrorV1> {',') -> Result<(), PoolV1PairForestTerminalFormatErrorV1> where L:FnMut(&Digest)->Result<u8,PoolV1PairForestAccountErrorV1>, A:FnMut(&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1> {').replace('pool_v1_pair_forest_output_lane_v1(&result.nullifier)','lane(&result.nullifier)').replace('encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)','after(&result.verified_afterstate)')
extra='\n'+body+'''
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_result_control(){
 let r=PoolV1PairForestTerminalResultV1{transition_kind:if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal},master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:NBN_digest(),verified_afterstate:NBN_common().lane_transition.candidate_afterstate};
 let l=if kani::any::<bool>() {Ok(kani::any::<u8>())}else{Err(NBN_any_PoolV1PairForestAccountErrorV1())};
 let a=if kani::any::<bool>() {Ok([0u8;688])}else{Err(NBN_any_PoolV1PairVerifierTransportErrorV1())};
 let stage=core::cell::Cell::new(0u8);
 let actual=NBN_result_cut(&r,|d|{assert_eq!(stage.get(),0);assert!(core::ptr::eq(d,&r.nullifier));stage.set(1);l},|x|{assert_eq!(stage.get(),1);assert!(core::ptr::eq(x,&r.verified_afterstate));stage.set(2);a});
 let zero=r.master_account==[0;32]||r.selected_lane_account==[0;32];
 let expected=if zero {Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}else{match l {Err(e)=>Err(PoolV1PairForestTerminalFormatErrorV1::Account(e)),Ok(lane)=>if r.output_lane!=lane {Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch)}else{a.map(|_|()).map_err(PoolV1PairForestTerminalFormatErrorV1::Afterstate)}}};
 assert_eq!(actual,expected);assert_eq!(stage.get(),if zero{0}else if l.is_err()||l.ok()!=Some(r.output_lane){1}else{2});
}
'''
p.write_text(old+extra);(E/'NBN_RESULT_EXTEND.json').write_text(json.dumps(dict(source=p.name,previous_sha256=hashlib.sha256(old.encode()).hexdigest(),frozen_revision=rev,source_path=path,source_function='validate_result',child_cuts=['same nullifier lane','same entire verified_afterstate encoder'],unwind=1881,no_stubs=True,credit='Kani selected control property only; KDX broader model fidelity unresolved'),indent=2)+'\n')
