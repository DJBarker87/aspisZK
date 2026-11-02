"""Whole frozen dot body and exact caller-domain structural binding."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index'];p=Path('crates/aspis-core/src/field.rs')
assert sha(p)==json.loads((D/'resume17/deployed-source-pins.json').read_text())[str(p)]
a=next(x for x in index(p.read_text())if x['name']=='qm31_m31_dot')
expected='''{
assert_eq!(weights.len(),values.len());
if weights.len() <= 4 {
let mut raw=[0u64;4];let mut index=0usize;
while index<weights.len(){let weight=weights[index];let value=u64::from(values[index].0);
raw[0]+=u64::from(weight.c0.a.0)*value;raw[1]+=u64::from(weight.c0.b.0)*value;
raw[2]+=u64::from(weight.c1.a.0)*value;raw[3]+=u64::from(weight.c1.b.0)*value;index+=1;}
return QM31{c0:CM31::new(M31::reduce_u64(raw[0]),M31::reduce_u64(raw[1])),c1:CM31::new(M31::reduce_u64(raw[2]),M31::reduce_u64(raw[3])),};}
let mut sums=[0u64;4];for start in (0..weights.len()).step_by(4){
let end=core::cmp::min(start+4,weights.len());let mut raw=[0u64;4];
for index in start..end{let value=values[index].0 as u64;let weight=weights[index];
raw[0]+=weight.c0.a.0 as u64*value;raw[1]+=weight.c0.b.0 as u64*value;
raw[2]+=weight.c1.a.0 as u64*value;raw[3]+=weight.c1.b.0 as u64*value;}
for index in 0..4{sums[index]+=M31::reduce_u64(raw[index]).0 as u64;}}
QM31{c0:CM31::new(M31::reduce_u64(sums[0]),M31::reduce_u64(sums[1])),c1:CM31::new(M31::reduce_u64(sums[2]),M31::reduce_u64(sums[3])),}}
'''
assert tokens(a['body'])==tokens(expected)
reference=json.loads((R/'REFERENCE-PROJECTED-D547.json').read_text())
assert 'reference_field.qm31_m31_dot' in [x['declaration']for x in reference['declarations']]
caller=Path('crates/aspis-statement/src/state_only_poseidon.rs');c=next(x for x in index(caller.read_text())if x['name']=='interpolated_internal_pair')
assert tokens(c['body']).count('qm31_m31_dot')==2
steps=[
('assert lengths and <=4 branch','dot7_source_entry15','Both only reached op227 calls have weights and constants of length7. Assertion true, fast branch unreachable. No claim about other lengths.'),
('step_by(4), min, inner ranges','dot7_ordered_partition15, dot7_block_indices15','Starts0,4, ends4,7. Exact range enumeration0,1,2,3 then4,5,6. Each index in7; each chunk resets raw to zero. Iterator cloning/Step/next and bounds follow the reached Range/StepBy source catalogue; compiler lowering V370 retained.'),
('four component updates','dot_cell554','Value read/cast first, weight second, then c0.a,c0.b,c1.a,c1.b in order. Unsigned casts zero extend, multiplies/additions wrap at64 under release. Never replace with canonical field reassociation; full raw32 payloads accepted.'),
('four block reductions','dot_reduce554','For each block, reduce raw[0..3] separately, cast each reduced result to64, add into corresponding sums, retain each array write. Two reduction levels stay distinct.'),
('final two CM31 constructors','dot_finish554','Reduce sums0,1, construct c0, reduce sums2,3, construct c1, then QM31 record. Complete Result equality includes error and divergence tags.'),
('borrow/drop paths','owned arrays in interpreter','Slice reads immutable; raw and sums indexed writes direct. No iterator-provided mutable loan/restoration is discarded. Copy QM31/M31/u64 has no user drop; wrapper erasure and primitive memory semantics remain V370/D381/D386.')]
x=dict(function='qm31_m31_dot',source=dict(path=str(p),sha256=sha(p),item=a,whole_body_tokens_checked=True),callers=dict(path=str(caller),sha256=sha(caller),item=c,reachable_calls=2,domain='seven weights and seven raw M31 constants'),source_steps=[dict(source=s,model=m,argument=v)for s,m,v in steps],reference=dict(receipt='N79167',comparison='REFERENCE-PROJECTED-D547.json',comparison_sha256=sha(R/'REFERENCE-PROJECTED-D547.json')),interpreter='PV_B3P_Association554227.dot_source554',theorem='PV_B3P_Association554227.dot_source_link554',feature_profile='ct-host-prover/release; unchanged deployed graph and source pins reused from N79167',route='Lean equality + own-1 structural',retained='whole std catalogue, D188 differentials, matrix, callback, V370/D381/D386',status='pending focused equality; no credit yet')
(R/'DOT-SOURCE-D554.json').write_text(json.dumps(x,indent=2)+'\n');print('whole dot body checked; exact two seven-element callers retained')
