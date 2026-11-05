from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
prefix='    state[0] = pow5(state[0].add(constant));';tail='    internal_linear_lazy(&mut state);\n    state';assert prefix in src and tail in src
prefixcut=prefix.replace('pow5(state[0].add(constant))','NIH_power_reply(state[0].add(constant),log)')
tailcut=tail.replace('internal_linear_lazy(&mut state)','NIH_internal_reply(&mut state,log)')
assert prefixcut.replace('NIH_power_reply(state[0].add(constant),log)','pow5(state[0].add(constant))')==prefix
assert tailcut.replace('NIH_internal_reply(&mut state,log)','internal_linear_lazy(&mut state)')==tail
out='''
struct NIH_PowerLog{input:[u32;4],reply:QM31,calls:usize}
fn NIH_power_reply(value:QM31,log:&mut NIH_PowerLog)->QM31{log.input=words(value);log.calls+=1;log.reply}
fn NIH_internal_prefix(mut state:[QM31;16],constant:QM31,log:&mut NIH_PowerLog)->[QM31;16]{
'''+prefixcut+'''
 state
}
struct NIH_InternalLog{input:[QM31;16],reply:[QM31;16],calls:usize}
fn NIH_internal_reply(state:&mut[QM31;16],log:&mut NIH_InternalLog){log.input=*state;log.calls+=1;*state=log.reply;}
fn NIH_internal_tail(mut state:[QM31;16],log:&mut NIH_InternalLog)->[QM31;16]{
'''+tailcut+'''
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_round_prefix(){let before:[QM31;16]=core::array::from_fn(|_|canonical());let constant=canonical();let reply=canonical();let mut log=NIH_PowerLog{input:kani::any(),reply,calls:0};let after=NIH_internal_prefix(before,constant,&mut log);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);assert_eq!(log.calls,1);assert_eq!(log.input[k],((u64::from(words(before[0])[k])+u64::from(words(constant)[k]))%u64::from(P)) as u32);assert_eq!(words(after[j])[k],words(if j==0{reply}else{before[j]})[k] ^ if cfg!(NIH_invert){1}else{0});assert_eq!(words(log.reply)[k],words(reply)[k]);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_round_tail(){let before:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let reply:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let mut log=NIH_InternalLog{input:core::array::from_fn(|_|q(kani::any())),reply,calls:0};let after=NIH_internal_tail(before,&mut log);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);assert_eq!(log.calls,1);assert_eq!(words(log.input[j])[k],words(before[j])[k]);assert_eq!(words(log.reply[j])[k],words(reply[j])[k]);assert_eq!(words(after[j])[k],words(reply[j])[k] ^ if cfg!(NIH_invert){1}else{0});}
'''
p=E/'NIH_internal.rs.txt';assert 'fn NIH_internal_prefix'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_INTERNAL_ROUND_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,prefix=prefix,prefix_cut=prefixcut,tail=tail,tail_cut=tailcut,reverse_erasure=True,power_stub='NIH_power_reply paired NHU_Pow5.result/domains, SAME canonical state0+constant',linear_stub='NIH_internal_reply paired NIH_InternalTotal.result, SAME canonical post-pow5 state, canonical full result instantiated from packet',modifies='prefix selected state0 and local log; tail local state overwritten by SAME logged packet reply and input/call fields; no static or function pointer'),indent=2)+'\n')
x=json.loads((E/'NIH_L058.json').read_text());x['sources'].append('NIH_INTERNAL_ROUND_ERASURE.json');(E/'NIH_L058.json').write_text(json.dumps(x,indent=2)+'\n')
