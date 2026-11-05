from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
start=src.index('fn leading_pair_packed(');end=src.index('\n}',start)+2;body=src[start:end]
absorb='        state[lane] = state[lane].add(openings.xor12_z[lane]);';assert absorb in body
cut=absorb.replace('openings.xor12_z[lane]','xor[lane]');assert cut.replace('xor[lane]','openings.xor12_z[lane]')==absorb
middle='external_linear_lazy(&mut state);';assert middle in body
full='full_round_m31_constants(state, EXTERNAL_INITIAL[0])';assert full in body
last='''full_round_m31_constants_packed(
        full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
        EXTERNAL_INITIAL[1],
    )''';assert last in body
out='''
fn NIH_leading_absorb(state:&mut[QM31;16],xor:&[QM31;16],iter:&mut core::ops::Range<usize>){if let Some(lane)=iter.next(){
'''+cut+'''
}}
struct NIH_LeadLog{linear_input:[QM31;16],linear_reply:[QM31;16],full_input:[QM31;16],full_reply:[QM31;16],full_constants:[u32;16],packed_input:[QM31;16],packed_reply:[QM31;4],packed_constants:[u32;16],calls:usize}
fn NIH_lead_linear(state:&mut[QM31;16],log:&mut NIH_LeadLog){assert_eq!(log.calls,0);log.linear_input=*state;log.calls+=1;*state=log.linear_reply;}
fn NIH_lead_full(state:[QM31;16],constants:[u32;16],log:&mut NIH_LeadLog)->[QM31;16]{assert_eq!(log.calls,1);log.full_input=state;log.full_constants=constants;log.calls+=1;log.full_reply}
fn NIH_lead_packed(state:[QM31;16],constants:[u32;16],log:&mut NIH_LeadLog)->[QM31;4]{assert_eq!(log.calls,2);log.packed_input=state;log.packed_constants=constants;log.calls+=1;log.packed_reply}
fn NIH_leading_mid(mut state:[QM31;16],log:&mut NIH_LeadLog)->[QM31;16]{
 NIH_lead_linear(&mut state,log);
 NIH_lead_full(state,EXTERNAL_INITIAL[0],log)
}
fn NIH_leading_last(state:[QM31;16],log:&mut NIH_LeadLog)->[QM31;4]{NIH_lead_packed(state,EXTERNAL_INITIAL[1],log)}
fn NIH_lead_log(calls:usize)->NIH_LeadLog{NIH_LeadLog{linear_input:core::array::from_fn(|_|q(kani::any())),linear_reply:core::array::from_fn(|_|q(kani::any())),full_input:core::array::from_fn(|_|q(kani::any())),full_reply:core::array::from_fn(|_|q(kani::any())),full_constants:kani::any(),packed_input:core::array::from_fn(|_|q(kani::any())),packed_reply:core::array::from_fn(|_|q(kani::any())),packed_constants:kani::any(),calls}}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_leading_prefix(){let mut state:[QM31;16]=core::array::from_fn(|_|canonical());let before=state;let xor:[QM31;16]=core::array::from_fn(|_|canonical());let start:usize=kani::any();kani::assume(start<=RATE);let mut iter=start..RATE;NIH_leading_absorb(&mut state,&xor,&mut iter);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);let expected=if start<RATE&&j==start{((u64::from(words(before[j])[k])+u64::from(words(xor[j])[k]))%u64::from(P)) as u32}else{words(before[j])[k]};assert_eq!(iter.start,if start<RATE{start+1}else{RATE});assert_eq!(iter.end,RATE);assert_eq!(words(state[j])[k],expected ^ if cfg!(NIH_invert){1}else{0});}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_leading_middle(){let before:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let mut log=NIH_lead_log(0);let linear=log.linear_reply;let full=log.full_reply;let out=NIH_leading_mid(before,&mut log);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);assert_eq!(log.calls,2);assert_eq!(words(log.linear_input[j])[k],words(before[j])[k]);assert_eq!(words(log.full_input[j])[k],words(linear[j])[k]);assert_eq!(log.full_constants[j],EXTERNAL_INITIAL[0][j]);assert_eq!(words(log.linear_reply[j])[k],words(linear[j])[k]);assert_eq!(words(log.full_reply[j])[k],words(full[j])[k]);assert_eq!(words(out[j])[k],words(full[j])[k] ^ if cfg!(NIH_invert){1}else{0});}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_leading_final(){let before:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let mut log=NIH_lead_log(2);let reply=log.packed_reply;let out=NIH_leading_last(before,&mut log);let j:usize=kani::any();let k:usize=kani::any();let r:usize=kani::any();kani::assume(j<16&&k<4&&r<4);assert_eq!(log.calls,3);assert_eq!(words(log.packed_input[j])[k],words(before[j])[k]);assert_eq!(log.packed_constants[j],EXTERNAL_INITIAL[1][j]);assert_eq!(words(log.packed_reply[r])[k],words(reply[r])[k]);assert_eq!(words(out[r])[k],words(reply[r])[k] ^ if cfg!(NIH_invert){1}else{0});}
'''
p=E/'NIH_internal.rs.txt';assert 'fn NIH_leading_absorb'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_LEADING_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,original=body,absorb=absorb,absorb_cut=cut,linear_call=middle,full_call=full,tail=last,reverse_erasure=True,call_substitution={'external_linear_lazy':'NIH_lead_linear','full_round_m31_constants':'NIH_lead_full','full_round_m31_constants_packed':'NIH_lead_packed'},domains='SAME canonical z/xor12_z; actual RATE8 one-iteration range; exact read-only frozen EXTERNAL_INITIAL rows0/1; all packet replies derived by completed layer/round packets',modifies='local state selected lane in absorb; local log inputs/constants/counter; final returns SAME logged reply unchanged; immutable openings and constant table'),indent=2)+'\n')
x=json.loads((E/'NIH_L058.json').read_text());x.update(attempt='NIH_L066',module='leading pair source stage inputs',sources=['NIH_update_internal.py','NIH_internal.rs.txt','NIH_LEADING_ERASURE.json']);(E/'NIH_L066.json').write_text(json.dumps(x,indent=2)+'\n')
