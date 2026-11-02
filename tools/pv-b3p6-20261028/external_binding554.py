"""Whole source comparison and per-step external-layer structural binding."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index'];p=Path('crates/aspis-statement/src/state_only_poseidon.rs')
assert sha(p)==json.loads((D/'resume17/deployed-source-pins.json').read_text())[str(p)]
a=next(x for x in index(p.read_text())if x['name']=='external_linear_lazy')
expected='''{
let mut group=0usize;while group<4{let start=4*group;
let input=[state[start],state[start+1],state[start+2],state[start+3],];
let input=input.map(extension_limbs);let mut output=0usize;
while output<4{let raw=core::array::from_fn(|limb|{
let a=u64::from(input[0][limb]);let b=u64::from(input[1][limb]);
let c=u64::from(input[2][limb]);let d=u64::from(input[3][limb]);
match output{0=>2*a+3*b+c+d,1=>a+2*b+3*c+d,2=>a+b+2*c+3*d,3=>3*a+b+c+2*d,_=>unreachable!(),}});
state[start+output]=extension_from_raw_limbs(raw);output+=1;}group+=1;}
let sums:[[u64;4];4]=core::array::from_fn(|column|{core::array::from_fn(|limb|{
u64::from(extension_limbs(state[column])[limb])+u64::from(extension_limbs(state[4+column])[limb])+u64::from(extension_limbs(state[8+column])[limb])+u64::from(extension_limbs(state[12+column])[limb])})});
let mut index=0usize;while index<POSEIDON2_WIDTH{let limbs=extension_limbs(state[index]);state[index]=extension_from_raw_limbs(core::array::from_fn(|limb|{u64::from(limbs[limb])+sums[index&3][limb]}));index+=1;}}
'''
assert tokens(a['body'])==tokens(expected)
ref=json.loads((R/'REFERENCE-PROJECTED-D547.json').read_text());required=['reference_poseidon.external_linear_lazy','reference_poseidon.external_group227','reference_poseidon.global_sums227','reference_poseidon.add_global227']
assert all(n in [x['declaration']for x in ref['declarations']]for n in required)
steps=[
('groups0..3, start4*g, four state snapshots','external_source554 group prefix','Exact group order0,1,2,3 and input indices0..15. Each input is copied before the group writes; no later group reads an earlier group cell.'),
('input.map(extension_limbs)','raw_input550','Reused ordered4 map/from_fn source argument and raw_input_continuation550. All array lengths and indices4 fixed; owned input snapshot persists for every output.'),
('output0..3, limb0..3','raw_row550 and raw_limb_zero/one/two/three550','Four distinct match trees with left-associated wrapping64 sums and products; no signed or field reassociation. Match default unreachable because output<4. Raw cell/row complete Result equalities previously accepted.'),
('extension_from_raw_limbs(raw), state[start+output]','external_group_source554 and sixteen local stores in external_source554','All four reductions/reconstructions occur in output order. Representing the four writes after the helper returns uses the immutable input snapshot, and the proved total fixed-index row/reconstruction calls; no intermediate write is read. No error can observe a partially updated local group. V370 allocation/abort and compiler semantics remain named.'),
('nested from_fn(column)(limb) for sums','external_sums_source554','Column-major0..3 then limb-major0..3, each scalar adds rows0,4,8,12+column in source order. Immutable repeated state reads use cached q snapshots only within this no-write phase. All indices<16; extension_limbs and widening are pure total; retaining each repeated extension call. Never shift these reads into the output-write pass.'),
('index0..15, sums[index&3]','external_source554 output pass','The mask yields0,1,2,3 repeated four times. The immutable sums columns are cached at first use, unchanged thereafter. All sixteen sequential state reads and writes retained; each read uses the latest state. Since different indices are written, the cell is its pre-pass value; no restoration omitted.'),
('from_fn limb addition then reconstruction','external_add_source554','Exactly four limb projections, zero extensions, corresponding sum reads, wrapping additions and extension_from_raw_limbs call; named external_add_reference554.'),
('iteration/drop/error paths','fixed loops plus existing four-element array model','Bounds: group/output/limb<4, start+output<16, column+12<16, index<16, index&3<4. Counters cannot overflow. Raw QM31/M31/u64 Copy carriers have no source drop effect. Source writes are direct array indexing, never a discarded iterator backward continuation. Whole pre-inline std catalogue and native differential still required by final closure.')]
x=dict(function='external_linear_lazy',source=dict(path=str(p),sha256=sha(p),item=a,whole_body_tokens_checked=True),reference=dict(receipt='N79167',comparison='REFERENCE-PROJECTED-D547.json',comparison_sha256=sha(R/'REFERENCE-PROJECTED-D547.json'),complete_declarations=required),source_steps=[dict(source=s,model=m,argument=v)for s,m,v in steps],interpreter='PV_B3P_Association554227.external_source554',theorem='PV_B3P_Association554227.external_source_link554',local_stores=list(range(16)),global_stores=list(range(16)),domain='all raw16 QM31 inputs; no canonicality or bounded-limb hypothesis',feature_profile='deployed ct-host-prover/release; resolved features and source hashes from N79167',route='Lean equality + own-1 structural',retained='whole std/D188/differential/matrix/callback, V370/D381/D386',status='pending focused helper and whole Result equalities; no credit yet')
(R/'EXTERNAL-SOURCE-D554.json').write_text(json.dumps(x,indent=2)+'\n');print('entire source checked; sixteen local and sixteen global state writes mapped')
