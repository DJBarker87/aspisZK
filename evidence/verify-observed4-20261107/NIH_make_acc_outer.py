from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
body=src[src.index('fn internal_linear_lazy('):src.index('\n#[inline(never)]\nfn full_round(',src.index('fn internal_linear_lazy('))]
start=body.index('        let limbs = extension_limbs(state[lane]);');end=body.index('\n    }',start);outer=body[start:end]
inner='''        while limb < 4 {
            part_sum[limb] += u64::from(limbs[limb]);
            limb += 1;
        }''';assert inner in outer
cut=outer.replace(inner,'        NIH_acc_reply(part_sum,limbs,&mut limb,log);')
assert cut.replace('        NIH_acc_reply(part_sum,limbs,&mut limb,log);',inner)==outer
out='''
struct NIH_AccLog{before:[u64;4],words:[u32;4],reply:[u64;4],start:usize,calls:usize}
fn NIH_acc_reply(part_sum:&mut[u64;4],limbs:[u32;4],limb:&mut usize,log:&mut NIH_AccLog){log.before=*part_sum;log.words=limbs;log.start=*limb;log.calls+=1;*part_sum=log.reply;*limb=4;}
fn NIH_acc_outer(state:&[QM31;16],part_sum:&mut[u64;4],mut lane:usize,log:&mut NIH_AccLog)->usize{if lane<POSEIDON2_WIDTH{
'''+cut+'''
}lane}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_internal_acc_outer(){let state:[QM31;16]=core::array::from_fn(|_|canonical());let mut part:[u64;4]=kani::any();let before=part;let reply:[u64;4]=kani::any();let lane:usize=kani::any();kani::assume(lane>=1&&lane<=16);let mut log=NIH_AccLog{before:kani::any(),words:kani::any(),reply,start:kani::any(),calls:0};let next=NIH_acc_outer(&state,&mut part,lane,&mut log);let k:usize=kani::any();kani::assume(k<4);assert_eq!(next,if lane<16{lane+1}else{16});assert_eq!(log.calls,if lane<16{1}else{0});if lane<16{assert_eq!(log.before[k],before[k]);assert_eq!(log.words[k],words(state[lane])[k]);assert_eq!(log.start,0);}assert_eq!(part[k],(if lane<16{reply[k]}else{before[k]}) ^ if cfg!(NIH_invert){1}else{0});assert_eq!(log.reply[k],reply[k]);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_leading_packet(){if kani::any::<bool>(){NIH_leading_prefix();}else{NIH_leading_tail_packet();}}
'''
p=E/'NIH_internal.rs.txt';assert 'fn NIH_internal_acc_outer'not in p.read_text();p.write_text(p.read_text()+out)
p=E/'NIH_copy.rs.txt';s=p.read_text().replace('fn NIH_outer_exhausted(){NIH_outer_done::<16>();NIH_outer_done::<64>();}','fn NIH_outer_exhausted(){if kani::any::<bool>(){NIH_outer_done::<16>();}else{NIH_outer_done::<64>();}}');p.write_text(s)
(E/'NIH_INTERNAL_ACC_OUTER_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,original=outer,cut=cut,inner=inner,reverse_erasure=True,domain='1<=lane<=16, canonical immutable state; raw part/reply arbitrary; model inner packet supplies 61P bounds on the SAME before/reply',inner_packet='K055/056 one raw limb iteration plus original JGj_InternalAccLimbs/AccState induction; start0/exhausted4',modifies='local part_sum from logged inner reply, lane scalar, local log only; input state immutable',reason='explicit native outer-loop association in addition to the inner limb and tail-lane certificates'),indent=2)+'\n')
x=json.loads((E/'NIH_L066.json').read_text());x['sources'].append('NIH_INTERNAL_ACC_OUTER_ERASURE.json');(E/'NIH_L066.json').write_text(json.dumps(x,indent=2)+'\n')
p=E/'NIH_leading_queue.py';s=p.read_text();start=s.index('jobs=');end=s.index('\nfor n,name,negative',start);jobs=[(95,'pool_v1::pair_forest_copy_terminal::NIH_native::NIH_outer_exhausted',False),(96,'pool_v1::pair_forest_copy_terminal::NIH_native::NIH_outer_exhausted',True),(97,'state_only_poseidon::NIH_internal_native::NIH_internal_acc_outer',False),(98,'state_only_poseidon::NIH_internal_native::NIH_internal_acc_outer',True),(99,'state_only_poseidon::NIH_internal_native::NIH_leading_packet',False),(100,'state_only_poseidon::NIH_internal_native::NIH_leading_packet',True)];s=s[:start]+'jobs='+repr(jobs)+s[end:];p.write_text(s)
