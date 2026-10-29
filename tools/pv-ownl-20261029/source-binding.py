"""Read-only ordered source/invariant checks; never promoted to whole refinement."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownl-20261029'
def source(p):return subprocess.check_output(['git','show','HEAD:'+p],text=True)
def function(s,name,start=0):
 a=s.index(name,start);b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
specs=[
 ('scalar_scale','crates/aspis-core/src/field.rs','pub fn mul_m31(self, rhs: M31) -> CM31', ['a: self.a.mul(rhs)','b: self.b.mul(rhs)'],'Scale.cmScale'),
 ('tower_scale','crates/aspis-core/src/field.rs','pub fn mul_m31(self, rhs: M31) -> QM31',['c0: self.c0.mul_m31(rhs)','c1: self.c1.mul_m31(rhs)'],'Scale.canonical'),
 ('helper_call','crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs','pub fn build_pool_v1_pair_forest_copy_helper_v1(',['pool_v1_pair_forest_copy_rows_v1(trace, append_index, lambda)?','build_copy_logup_helper(&rows, chi).map_err'],'HelperRows.vector_canonical'),
 ('helper','crates/aspis-statement/src/logup.rs','pub fn build_copy_logup_helper(',['Vec::with_capacity(rows.len())','rows.iter().enumerate()','let mut value = QM31::ZERO','row.producer_values.into_iter().zip(row.producer_weights)','if weight != M31::ZERO','value = value.add(','chi.sub(producer_value)','.try_inv()','LogUpSide::Producer','.mul_m31(weight)','row.consumer_values.into_iter().zip(row.consumer_weights)','if weight != M31::ZERO','value = value.sub(','chi.sub(consumer_value)','.try_inv()','LogUpSide::Consumer','.mul_m31(weight)','helper.push(value)','Ok(helper)'],'HelperSlots.slots_canonical; HelperRows.vector_canonical'),
 ('sampler_pass','crates/aspis-core/src/r0_transcript.rs','fn base_p_digits(',['core::array::from_fn','let mut remainder = 0u64','rank.iter_mut().rev()','let dividend =','*limb = (dividend / u64::from(P)) as u32','remainder = dividend % u64::from(P)','remainder as u32'],'SampleWord.rem_bound; SampleCanon.pass_canonical'),
 ('sampler','crates/aspis-core/src/r0_transcript.rs','pub fn qm31_sample(',['base_p_digits(reduce_rank(block_rank(block), P4))','decode4([d[0], d[1], d[2], d[3]])'],'SampleCanon.sample_canonical'),
 ('caller','crates/aspis-prover/src/state_only_candidate_prefix.rs','fn build_pair_forest_mode(',['build_with_helper_mode(','build_pool_v1_pair_forest_copy_helper_v1(','&compiled.trace','public.transition().live_snapshot.next_pair_index','lambda','chi'],'same helper selected by consuming source'),
]
rows=[]
for name,path,needle,tokens,theorem in specs:
 s=source(path);body=function(s,needle);pos=-1
 for t in tokens:pos=body.index(t,pos+1)
 rows.append(dict(name=name,path=path,file_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),body=body,ordered_tokens=tokens,model_theorem=theorem))
# All deployed library source pins must still agree with current source.
pins=json.loads((E/'crate-source-pins.json').read_text())
for p in pins['files']:assert hashlib.sha256(subprocess.check_output(['git','show','HEAD:'+p['path']])).hexdigest()==p['sha256']
r=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),rows=rows,verified_crate_files=len(pins['files']),classification='partial structural source/invariant binding under own-1; not a full consuming execution refinement',retained=['V370/D381/D386','rdea-1'],differences=['Helper model Option forgets ActivePole row/side and outer error tags; canonicality theorem is successful-output only.','Source fixed two-slot arrays traverse their ordered List views; generic invariant admits every length.','HelperRows also proves host array-store invariant, but actual point_claims consumer selects statement logup Vec helper.','Sampler pass is high-word-first and retains every quotient. Rank reduction may be arbitrary for output canonicality.','Sampler model constructs first four digits; native computes eight then selects first four. Future-pass erasure and byte/array carrier still need source-execution composition.'])
(E/'source-binding.json').write_text(json.dumps(r,indent=2)+'\n');print('checked',len(rows),'ordered bodies and',len(pins['files']),'unchanged crate files')
