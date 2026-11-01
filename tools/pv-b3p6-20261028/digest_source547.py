"""Statement-by-statement source association; no compiled-code claim."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18'
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=Path('crates/aspis-r1-cost-probe/src/host_terminal.rs');assert sha(p)==json.loads((D/'resume17/deployed-source-pins.json').read_text())[str(p)]
a=next(x for x in index(p.read_text())if x['name']=='public_digest_lanes')
expected='''{let mut digests=[QM31::ZERO;DIGEST_ELEMS];
add_digest_binding(&mut digests,selectors.row(56*16+11),&openings.z,0,&public.anchor,false,);
add_digest_binding(&mut digests,selectors.row(26*16+11),&openings.z,0,&public.nullifier,false,);
if let Some(recipient)=public.recipient {add_digest_binding(&mut digests,selectors.row(29*16+11),&openings.z,0,&recipient,false,);}
add_digest_binding(&mut digests,selectors.row(32*16+11),&openings.z,0,&public.change,false,);
let source=public.transition.live_snapshot;let after=public.transition.candidate_afterstate;
for level in 0..20 {let block=34+level;if ((source.next_pair_index>>level)&1)==0 {
add_digest_binding(&mut digests,selectors.row(block*16),&openings.z,RATE,&empty_root(level),true,);
}else {add_digest_binding(&mut digests,selectors.row(block*16+12),&openings.z,0,&source.frontier[level],false,);}}
add_digest_binding(&mut digests,selectors.row(53*16+11),&openings.z,0,&after.next_root,false,);
let carry=bounded_append_carry(source.next_pair_index);if carry<20 {
add_digest_binding(&mut digests,selectors.row((33+carry)*16+11),&openings.z,0,&after.next_frontier[carry],false,);}
digests}'''
assert tokens(a['body'])==tokens(expected)
steps=[
('initialize eight ZERO elements','digest_stage_00 prefix','Exact fixed carrier and ZERO constant; no allocation, external read or input restriction. Array.repeat source/copy lowering retained at V370.'),
('anchor, nullifier, optional recipient, change bindings in order','digest_stage_00..03','Exact row indices907,427,475,523, opened z, start0 and right_tweak=false. Recipient branches on the preserved Option, not a dummy value. Both variants restore the whole mutable digest array before the next call. add_digest_binding is the direct source row with total Result law; row helper remains named.'),
('snapshot and candidate copies, Range0..20','digest_level11 via range_loop13','Immutable same-origin public carriers, PublicInput543 round trips retain all fields. range_loop_binding13 preserves ascending20 iterations and every Result error/divergence. Increment and block34+level cannot overflow. Range/Step source argument is SUM-SOURCE-BINDING-D542; compiler clone/drop retained V370.'),
('test source.next_pair_index bit level, choose one digest update','digest_level11 branch','Same unsigned shift by level0..19, same AND1 and equality zero. Zero bit uses row(34+level)*16, start8 and identical empty_root(level), right_tweak=true. Nonzero uses row(34+level)*16+12, start0 and source.frontier[level], right_tweak=false. Only the selected branch is evaluated. The next iteration receives the entire restored output. No field-chain reassociation.'),
('next_root update; carry computation and optional next_frontier update','digest_stage_24','First row859, start0, next_root,false. Then identical bounded_append_carry(next_pair_index); exactly when carry<20 read next_frontier[carry] and row(33+carry)*16+11 and call the same source helper. Failure and return order retained; no afterstate read is moved before the guard. carry arithmetic and helper source rows remain named dependencies.'),
('return digests','native_public_digest15 final bind','All source stores occur through the direct mutable add_digest_binding row; every call returns/restores the full eight-element array before any continuation. No back/restoration continuation is discarded. No pointer escapes or custom Drop.')]
x=dict(function='public_digest_lanes',source=dict(path=str(p),sha256=sha(p),item=a,whole_body_tokens_checked=True),interpreter='PV_B3P_Native15227.native_public_digest15',theorem='PV_B3P_Association547227.public_digest_source_link547',steps=[dict(source=s,model=m,argument=t)for s,m,t in steps],domain='all SemanticPublic, openings and selectors carrier values; Option and carry guards retained, no field canonicality narrowing',laws=['native_public_digest_binding15','public_digest_source_loop_binding11','range_loop_binding13','public_digest_source_link547'],route='Lean complete-Result equality plus own-1 structural argument',features='ct-host-prover, exact source body has no cfg/cfg!; release overflow/debug checks off; fresh reference-schedule inputs graph',D188='Whole-array mutable restoration after every digest helper call, including both conditional branches; no iterator mutation in this body',retained='Named helper/dependency source rows, full std/D188/matrix/callback closure, source-to-machine V370/D381/D386. No endpoint or T changes.',status='pending focused receipt and fresh reference declaration comparison')
(R/'DIGEST-SOURCE-D547.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(bodies=1,steps=len(steps))))
