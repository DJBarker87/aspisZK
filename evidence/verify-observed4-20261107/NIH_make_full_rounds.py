from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
names=['full_round','full_round_m31_constants','full_round_packed','full_round_m31_constants_packed'];bodies={}
for name in names:
 start=src.index('fn '+name+'(');end=src.index('\n}',start)+2;bodies[name]=src[start:end]
qbody='''        state[lane] = pow5(state[lane].add(constants[lane]));'''
mbody='''        state[lane].c0.a = state[lane].c0.a.add(M31(constants[lane]));
        state[lane] = pow5(state[lane]);'''
for name,body in bodies.items():assert (mbody if 'm31_constants' in name else qbody) in body
qcut=qbody.replace('pow5(state[lane].add(constants[lane]))','NIH_power_reply(state[lane].add(constants[lane]),log)')
mcut=mbody.replace('pow5(state[lane])','NIH_power_reply(state[lane],log)')
assert qcut.replace('NIH_power_reply(state[lane].add(constants[lane]),log)','pow5(state[lane].add(constants[lane]))')==qbody
assert mcut.replace('NIH_power_reply(state[lane],log)','pow5(state[lane])')==mbody
lazytail='    external_linear_lazy(&mut state);\n    state';packedtail='    external_linear_packed(state)'
assert lazytail in bodies['full_round'] and lazytail in bodies['full_round_m31_constants'];assert packedtail in bodies['full_round_packed'] and packedtail in bodies['full_round_m31_constants_packed']
out='''
fn NIH_qm_lane(state:&mut[QM31;16],constants:&[QM31;16],iter:&mut core::ops::Range<usize>,log:&mut NIH_PowerLog){if let Some(lane)=iter.next(){
'''+qcut+'''
}}
fn NIH_m31_lane(state:&mut[QM31;16],constants:&[u32;16],iter:&mut core::ops::Range<usize>,log:&mut NIH_PowerLog){if let Some(lane)=iter.next(){
'''+mcut+'''
}}
fn NIH_full_prefix_window(m31:bool){let mut state:[QM31;16]=core::array::from_fn(|_|canonical());let before=state;let constants:[QM31;16]=core::array::from_fn(|_|canonical());let base:[u32;16]=core::array::from_fn(|_|{let w:u32=kani::any();kani::assume(w<P);w});let start:usize=kani::any();kani::assume(start<=16);let mut iter=start..16;let reply=canonical();let mut log=NIH_PowerLog{input:kani::any(),reply,calls:0};if m31{NIH_m31_lane(&mut state,&base,&mut iter,&mut log);}else{NIH_qm_lane(&mut state,&constants,&mut iter,&mut log);}let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);assert_eq!(iter.start,if start<16{start+1}else{16});assert_eq!(iter.end,16);assert_eq!(log.calls,if start<16{1}else{0});if start<16{let expected=if m31&&k!=0{words(before[start])[k]}else{((u64::from(words(before[start])[k])+u64::from(if m31{base[start]}else{words(constants[start])[k]}))%u64::from(P)) as u32};assert_eq!(log.input[k],expected);}assert_eq!(words(state[j])[k],words(if start<16&&j==start{reply}else{before[j]})[k] ^ if cfg!(NIH_invert){1}else{0});assert_eq!(words(log.reply)[k],words(reply)[k]);}
fn NIH_lazy_round_tail(mut state:[QM31;16],log:&mut NIH_InternalLog)->[QM31;16]{
'''+lazytail.replace('external_linear_lazy(&mut state)','NIH_internal_reply(&mut state,log)')+'''
}
struct NIH_PackedTailLog{input:[QM31;16],reply:[QM31;4],calls:usize}
fn NIH_external_packed_reply(state:[QM31;16],log:&mut NIH_PackedTailLog)->[QM31;4]{log.input=state;log.calls+=1;log.reply}
fn NIH_packed_round_tail(state:[QM31;16],log:&mut NIH_PackedTailLog)->[QM31;4]{
'''+packedtail.replace('external_linear_packed(state)','NIH_external_packed_reply(state,log)')+'''
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_full_qm_prefix(){NIH_full_prefix_window(false);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_full_m31_prefix(){NIH_full_prefix_window(true);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_full_lazy_tail(){let before:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let reply:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let mut log=NIH_InternalLog{input:core::array::from_fn(|_|q(kani::any())),reply,calls:0};let out=NIH_lazy_round_tail(before,&mut log);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);assert_eq!(log.calls,1);assert_eq!(words(log.input[j])[k],words(before[j])[k]);assert_eq!(words(out[j])[k],words(reply[j])[k] ^ if cfg!(NIH_invert){1}else{0});assert_eq!(words(log.reply[j])[k],words(reply[j])[k]);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_full_packed_tail(){let before:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let reply:[QM31;4]=core::array::from_fn(|_|q(kani::any()));let mut log=NIH_PackedTailLog{input:core::array::from_fn(|_|q(kani::any())),reply,calls:0};let out=NIH_packed_round_tail(before,&mut log);let j:usize=kani::any();let k:usize=kani::any();let r:usize=kani::any();kani::assume(j<16&&k<4&&r<4);assert_eq!(log.calls,1);assert_eq!(words(log.input[j])[k],words(before[j])[k]);assert_eq!(words(out[r])[k],words(reply[r])[k] ^ if cfg!(NIH_invert){1}else{0});assert_eq!(words(log.reply[r])[k],words(reply[r])[k]);}
'''
p=E/'NIH_internal.rs.txt';assert 'fn NIH_full_qm_prefix'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_FULL_ROUND_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,bodies=bodies,qm_prefix=qbody,m31_prefix=mbody,qm_cut=qcut,m31_cut=mcut,lazy_tail=lazytail,packed_tail=packedtail,reverse_erasure=True,modifies='one selected lane/cursor/local log in nonlinear step; tail logs exact same full input and returns packet reply unchanged',domains='canonical state16 and QM31 constants16 or bounded M31 constants16; arbitrary Range start<=16; power reply canonical, tail replies arbitrary raw instantiated by the closed layer packets',reused_identical_source_cuts={'qm_prefix':['full_round','full_round_packed'],'m31_prefix':['full_round_m31_constants','full_round_m31_constants_packed'],'lazy_tail':['full_round','full_round_m31_constants'],'packed_tail':['full_round_packed','full_round_m31_constants_packed']},stubs={'NIH_power_reply':'NHU_Pow5.result/domains on actual canonical sum','NIH_internal_reply':'NIH_ExternalLazy.result on same nonlinear state','NIH_external_packed_reply':'NIH_ExternalPacked.result on same nonlinear state'}),indent=2)+'\n')
x=json.loads((E/'NIH_L058.json').read_text());x['sources'].append('NIH_FULL_ROUND_ERASURE.json');(E/'NIH_L058.json').write_text(json.dumps(x,indent=2)+'\n')
