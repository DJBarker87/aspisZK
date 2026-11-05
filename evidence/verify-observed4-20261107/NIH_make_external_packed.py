from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
body=src[src.index('fn external_linear_packed('):src.index('\n#[inline(never)]\nfn internal_linear_lazy(',src.index('fn external_linear_packed('))]
start=body.index('        let start = 4 * group;');end=body.index('\n    }',start);group=body[start:end]
cut=group.replace('external_local_packed(input)','NIH_local_reply(input,log)')
assert cut.replace('NIH_local_reply(input,log)','external_local_packed(input)')==group
start=body.index('QM31::ZERO\n        .add(');end=body.index(';',start);sumexpr=body[start:end]
mapexpr='value.add(sum)';assert mapexpr in body
out='''
struct NIH_GroupLog{input:[[u32;4];4],reply:QM31,calls:usize}
fn NIH_local_reply(input:[QM31;4],log:&mut NIH_GroupLog)->QM31{log.input=input.map(words);log.calls+=1;log.reply}
fn NIH_group_cut(state:&[QM31;16],mut local_packed:[QM31;4],mut group:usize,log:&mut NIH_GroupLog)->([QM31;4],usize){if group<4{
'''+cut+'''
}(local_packed,group)}
fn NIH_sum_cut(local_packed:[QM31;4])->QM31{'''+sumexpr+'''}
fn NIH_map_cut(value:QM31,sum:QM31)->QM31{'''+mapexpr+'''}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_packed_group(){let state:[QM31;16]=core::array::from_fn(|_|canonical());let before:[QM31;4]=core::array::from_fn(|_|q(kani::any()));let reply=canonical();let group:usize=kani::any();kani::assume(group<=4);let mut log=NIH_GroupLog{input:kani::any(),reply,calls:0};let (out,next)=NIH_group_cut(&state,before,group,&mut log);let j:usize=kani::any();let k:usize=kani::any();let r:usize=kani::any();kani::assume(j<4&&k<4&&r<4);assert_eq!(next,if group<4{group+1}else{4});assert_eq!(log.calls,if group<4{1}else{0});if group<4{assert_eq!(log.input[r][k],words(state[4*group+r])[k]);}assert_eq!(words(out[j])[k],words(if j==group{reply}else{before[j]})[k] ^ if cfg!(NIH_invert){1}else{0});assert_eq!(words(log.reply)[k],words(reply)[k]);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_packed_sum(){let values:[QM31;4]=core::array::from_fn(|_|canonical());let out=words(NIH_sum_cut(values));let k:usize=kani::any();kani::assume(k<4);let total=u64::from(words(values[0])[k])+u64::from(words(values[1])[k])+u64::from(words(values[2])[k])+u64::from(words(values[3])[k]);assert_eq!(out[k],(total%u64::from(P)) as u32 ^ if cfg!(NIH_invert){1}else{0});}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_packed_map(){let value=canonical();let sum=canonical();let out=words(NIH_map_cut(value,sum));let k:usize=kani::any();kani::assume(k<4);let expected=((u64::from(words(value)[k])+u64::from(words(sum)[k]))%u64::from(P)) as u32;assert_eq!(out[k],expected ^ if cfg!(NIH_invert){1}else{0});}
'''
p=E/'NIH_internal.rs.txt';assert 'fn NIH_packed_group'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_EXTERNAL_PACKED_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),group=group,group_cut=cut,sum_expression=sumexpr,map_expression=mapexpr,reverse_erasure=True,modifies='group only local packed selected cell, group cursor and local log; sum/map pure record results',loop='one arbitrary group<=4; no whole-buffer unwinding; emitted JGj_PackedLoopTotal/FJe_PackedLoopValue induction',stub='NIH_local_reply paired NIH_LocalPacked.result; canonical original four operands and canonical packet reply'),indent=2)+'\n')
