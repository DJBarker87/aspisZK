"""Independent, exhaustive local source grammars for the new loop dossiers.
Named Lean laws carry semantic transformations. Grammar equality alone is never
credited as deployed dependency closure.
"""
from pathlib import Path
import json,re,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');I=json.loads((D/'resume9/body-inventory.json').read_text());O=D/'resume15'
patterns={
'reconstruct_10':'''{ let mut acc=view[9]; let mut index=9usize; while index>0 { index-=1; acc=acc.add(acc).add(view[index]); } acc }''',
'equality_value':'''{ let mut product=equality_factor(left[0],right[0]);let mut index=1usize;while index<left.len(){product=product.mul(equality_factor(left[index],right[index]));index+=1;}product }''',
'full_round':'''{for lane in 0..POSEIDON2_WIDTH {state[lane]=pow5(state[lane].add(constants[lane]));}external_linear_lazy(&mut state);state}''',
'full_round_packed':'''{for lane in 0..POSEIDON2_WIDTH {state[lane]=pow5(state[lane].add(constants[lane]));}external_linear_packed(state)}''',
'full_round_m31_constants':'''{for lane in 0..POSEIDON2_WIDTH {state[lane].c0.a=state[lane].c0.a.add(M31(constants[lane]));state[lane]=pow5(state[lane]);}external_linear_lazy(&mut state);state}''',
'full_round_m31_constants_packed':'''{for lane in 0..POSEIDON2_WIDTH {state[lane].c0.a=state[lane].c0.a.add(M31(constants[lane]));state[lane]=pow5(state[lane]);}external_linear_packed(state)}''',
'leading_pair_packed':'''{let mut state=openings.z;for lane in 0..RATE {state[lane]=state[lane].add(openings.xor12_z[lane]);}external_linear_lazy(&mut state);full_round_m31_constants_packed(full_round_m31_constants(state,EXTERNAL_INITIAL[0]),EXTERNAL_INITIAL[1],)}''',
'absorption_lanes_literal':'''{qm31_array!(16,lane,{let blocks=if lane<2 {fixed}else if lane<RATE {fixed.add(chunk_two)}else{fixed.add(chunk_two).add(chunk_eight).add(nodes)};low.mul(blocks).mul(openings[lane])})}''',
'occupancy_lanes_literal':'''{let occupied=opened[0];let inverse=opened[1];let one_minus=QM31::ONE.sub(occupied);let mut occupancy=[QM31::ZERO;12];let both=input_occupancy.add(output_occupancy);occupancy[0]=both.mul(occupied.mul(occupied.sub(QM31::ONE)));occupancy[1]=both.mul(opened[9].mul(inverse).sub(occupied));occupancy[2]=both.mul(one_minus.mul(inverse));for lane in 0..DIGEST_ELEMS {occupancy[3+lane]=both.mul(one_minus.mul(opened[2+lane]));}occupancy[11]=input_occupancy.mul(opened[10].mul(one_minus)).add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));occupancy}''',
'path_lanes_literal':'''{let bit=openings.z[0];let mut path=[QM31::ZERO;17];path[0]=path_selector.mul(bit.mul(bit.sub(QM31::ONE)));for lane in 0..DIGEST_ELEMS {let current=openings.z[1+lane];path[1+lane]=path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[lane].sub(current));path[1+DIGEST_ELEMS+lane]=path_selector.mul(bit).mul(openings.succ_z[RATE+lane].sub(current));}path}''',
'interpolate_three_constant_columns':'''{let mut output=[QM31::ZERO;POSEIDON2_WIDTH];let mut lane=0usize;while lane<POSEIDON2_WIDTH {output[lane]=QM31{c0:CM31::new(interpolate_three_constant_limb(weights[0].c0.a.0,weights[1].c0.a.0,weights[2].c0.a.0,column0[lane],column1[lane],column2[lane],),interpolate_three_constant_limb(weights[0].c0.b.0,weights[1].c0.b.0,weights[2].c0.b.0,column0[lane],column1[lane],column2[lane],),),c1:CM31::new(interpolate_three_constant_limb(weights[0].c1.a.0,weights[1].c1.a.0,weights[2].c1.a.0,column0[lane],column1[lane],column2[lane],),interpolate_three_constant_limb(weights[0].c1.b.0,weights[1].c1.b.0,weights[2].c1.b.0,column0[lane],column1[lane],column2[lane],),),};lane+=1;}output}''',
'sum_high':'''{let mut sum=QM31::ZERO;for range in ranges {for block in range.clone(){sum=sum.add(selectors.high[block]);}}sum}''',
'active_literal':'''{let mut sum=QM31::ZERO;let mut block=0usize;while block<64 {let mask=constants::ACTIVE_ROW_MASKS[block];if mask!=0 {sum=sum.add(self.high[block].mul(selector_mask_sum_16(&self.low,mask)));}block+=1;}sum}''',
}
patterns.update({
'poseidon_selectors': '{StateOnlyPoseidonSelectors{block:sum_high(selectors,&[0..57]),local:selectors.low,}}',
'add_schedule_lanes': '{let(initial,absorption)=semantic_initial_and_absorption(public,openings,selectors);add_preweighted(packed,0,&initial);add_preweighted(packed,16,&absorption);}',
})

rows=[]
for name,pattern in patterns.items():
 b=next(b for b in I['bodies']if b['key']==name+'#0');a=b['source']['tokens'];a=a[a.index('{'):];want=re.findall(r'\w+|[^\s]',pattern)
 if a!=want:
  import difflib
  print(name,list(difflib.ndiff(a,want))[:20]);raise SystemExit('grammar mismatch '+name)
 # Change one numeric literal where possible, otherwise a callee identifier.
 negative=want.copy();i=next((i for i,t in enumerate(want)if t.isdigit()),None)
 if i is None:
  i=want.index('add');negative[i]='sub'
 else:negative[i]=str(int(negative[i])+1)
 assert a!=negative
 rows.append(dict(function=name,complete_body_grammar=True,source_body_token_sha256=hashlib.sha256('\0'.join(a).encode()).hexdigest(),expected_grammar_sha256=hashlib.sha256('\0'.join(want).encode()).hexdigest(),negative_control=dict(changed_token_index=i,old=want[i],new=negative[i],rejected=True),evidence_class='source grammar check plus separately compiled named structural laws; no dependency closure credit'))
x=dict(rows=rows,all_source_tokens_covered=True,fully_composed_new_bound=0,machine_boundary='V370 / pending owner D381,D386 retained')
p=O/'source-grammar-checks.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==x
else:p.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(source_functions_checked=len(rows),matched_controls=len(rows),new_full_native_credit=0)))
