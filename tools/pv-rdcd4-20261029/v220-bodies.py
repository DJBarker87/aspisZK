"""Complete-body token checks and explicit own-1 associations, not a checker."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def tokens(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def function(s,marker):
 assert s.count(marker)==1,(marker,s.count(marker));a=s.index(marker);b=s.index('{',a);depth=0
 for m in lex.finditer(s,b):
  if m[0]=='{':depth+=1
  elif m[0]=='}':
   depth-=1
   if not depth:return s[a:m.end()]
 raise AssertionError(marker)
def tracked(p):return subprocess.check_output(['git','show','HEAD:'+p],cwd=R,text=True)
ref=json.load(open(R/'evidence/pv-rdcd-20261028/project-native-inputs.json'))['tools/pv-cb3-20261026/reference_polynomial.rs']['text']
field=tracked('crates/aspis-core/src/field.rs');root=tracked('crates/aspis-core/src/state_only_sumcheck.rs')
reconstruct=function(ref,'fn qm31_from_karatsuba_channel_sums(')
acc=function(ref,'fn qm31_accumulate_product_channels(');acc=acc[:acc.index('    sums[0][0]')]+'''for component in 0..3 {for channel in 0..3 {sums[component][channel] += left_components[component][channel].0 as u64 * right_components[component][channel].0 as u64;}} sums }'''
small='''fn qm31_sum_products_small<const N:usize>(left:[QM31;N],right:[QM31;N])->QM31 {debug_assert!(N>=2&&N<=4);let mut sums=[[0u64;3];3];let mut index=0usize;while index<N{sums=qm31_accumulate_product_channels(sums,left[index],right[index]);index+=1;}qm31_from_karatsuba_channel_sums(sums)}'''
wrapper='''pub fn qm31_sum_products3(left:[QM31;3],right:[QM31;3])->QM31{qm31_sum_products_small(left,right)}'''
evaluate='''pub fn evaluate_state_only_polynomial(polynomial:&StateOnlySumcheckPolynomial,challenge:QM31,)->QM31{let x2=challenge.square();let x3=challenge.mul(x2);let x4=x2.square();let powers=[challenge,x2,x3];let prepared_x4=PreparedQm31Multiplier::new(x4);let block_value=|block:usize|{let start=4*block;polynomial[start].add(qm31_sum_products3(powers,[polynomial[start+1],polynomial[start+2],polynomial[start+3],],))};let mut accumulator=block_value(6);let mut block=6usize;while block>0{block-=1;accumulator=prepared_x4.mul(accumulator).add(block_value(block));}accumulator}'''
checks=[
(field,'fn qm31_from_karatsuba_channel_sums(',reconstruct,['LazyReconstruct.component','LazyReconstruct.source'],'Three channel reads/reductions in order; two scalar subtractions for b; three component reconstructions; mul_by_r; c0 add then c1 sub/sub. Copy values have no user Drop.'),
(field,'fn qm31_accumulate_product_channels(',acc,['LazyPair.pair/finish','LazyCell.cell/changed_outer','LazyChannels.row_unroll/nine_unroll','LazyAccumulate.binding'],'Left-sum then right-sum before component arrays; all six component additions in order; nested row-major Range<usize> loops; read RHS factors, cast to u64, wrapping product; read/update inner destination then write changed outer destination. Final complete sums retained.'),
(field,'fn qm31_sum_products_small<',small,['LazyProducts.source/binding'],'N=3, release debug assertion disabled; initialize all nine zeros; three checked public array reads and complete accumulation stores; increment bounded0..3; reconstruct after loop.'),
(field,'pub fn qm31_sum_products3(',wrapper,['LazyProducts.source'],'Concrete N=3 forwarding; both Copy arrays remain in source order, no destructor branch.'),
(root,'pub fn evaluate_state_only_polynomial(',evaluate,['RadixBlock.index_bound/index_word_bound/binding','RadixLoop.binding/step_binding','V220.source_reference'],'square/mul/square in source order; construct three powers; prepare x4; closure start=4*block with exact four indexed coefficients; initialize block6; decrement before each multiply/add; return final accumulator after block0. All reachable indices bounded below28 and word overflow impossible. No external state or arbitrary callback added.')]
records=[]
for src,marker,expected,models,steps in checks:
 actual=function(src,marker);assert tokens(actual)==tokens(expected),marker
 records.append(dict(marker=marker,source_file_sha256=sha(src),body=actual,body_sha256=sha(actual),expected_body=expected,expected_sha256=sha(expected),token_sha256=sha(json.dumps(tokens(actual))),models=['R1Z.PV_RDCD4_'+x for x in models],statement_binding=steps))
out=dict(row='V220',records=records,original_owned_reference_sha256=sha(ref),qualification='Mechanical whole-body shape checks plus own-1 hand structural associations; NOT an original checker, not a pinned extraction generation chain, zero b3p6-1 reclassifications.',primitive_boundary='Rust integer/layout/drop and compiler execution V370/D381/D386 retained; complete Result interface unchanged',pending='Compile the source/owned-reference transport; confirm fixed initialized representation invariants and final object/source closure.')
(E/'v220-body-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('Five complete lazy/root bodies match recorded literals; original reference archived; no row credit yet.')
