"""Exact application source patterns for the selected-mask Result model.
A partial gate: field/library association and proof receipts are separate.
"""
from pathlib import Path
import json,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
a=runpy.run_path(str(D/'range-source.py'));span,tokens,sha=(a[k] for k in ['span','tokens','sha'])
p=S/'crates/aspis-core/src/state_only_hiding.rs';src=p.read_text()
checks=[
('fn cm31_mul_i(','''fn cm31_mul_i(value:CM31)->CM31{CM31::new(value.b.neg(),value.a)}''','MaskLeaves.i; FieldSource.CM31.new/M31.neg',
 'Read b, negate b, construct (neg b,a). All fields Copy; no user drop.'),
('fn cm31_mul_r(','''fn cm31_mul_r(value:CM31)->CM31{CM31::new(value.a.double().sub(value.b),value.a.add(value.b.double()))}''','MaskLeaves.r',
 'Double a, subtract b; double b, add a; construct ordered pair. No error branch beyond callees.'),
('fn mul_tower_basis(','''fn mul_tower_basis(value:QM31,coordinate:usize)->QM31{match coordinate{0=>value,1=>QM31{c0:cm31_mul_i(value.c0),c1:cm31_mul_i(value.c1),},2=>QM31{c0:cm31_mul_r(value.c1),c1:value.c0,},3=>QM31{c0:cm31_mul_i(cm31_mul_r(value.c1)),c1:cm31_mul_i(value.c0),},_=>panic!("state-only hiding tower coordinate out of range"),}}''','MaskLeaves.tower; OwnedMaskLeaves.tower',
 'Four match arms and terminal panic preserved. Reachable column &3 bounds exclude panic; no all-coordinate success claim.'),
('fn selected_mask_linears(','''fn selected_mask_linears(point:&[QM31;STATE_ONLY_HIDING_SUMCHECK_ROUNDS])->(QM31,QM31){let mut suffix=QM31::ZERO;let mut weighted=QM31::ZERO;for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev(){suffix=suffix.add(point[variable]);if variable!=0{weighted=weighted.add(suffix);}}(suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))),)}''','OwnedMaskLinearsEq.source; MaskLinearsFinite.source',
 'Zero states; reversed range; index read then suffix write; guarded weighted write; four scalar products and two ordered sums. The final pair is constructed left to right.'),
('fn mask_power_26(','''fn mask_power_26(value:QM31)->QM31{let x2=value.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();x16.mul(x8).mul(x2)}''','MaskLeaves.power',
 'Four squares, then x16*x8, then product*x2; no generic exponentiation substitute.'),
('pub fn state_only_selected_mask_value(','''pub fn state_only_selected_mask_value(c1:&[QM31;STATE_ONLY_HIDING_C1_COLUMNS],mask_only_c1:&[QM31;STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],explicit_g:QM31,point:&[QM31;STATE_ONLY_HIDING_SUMCHECK_ROUNDS],)->QM31{let(linear,explicit_linear)=selected_mask_linears(point);let mut coefficients=[QM31::ZERO;STATE_ONLY_HIDING_FACTOR_DEGREE+1];for column in 0..STATE_ONLY_HIDING_C1_COLUMNS{coefficients[usize::from(FACTOR_EXPONENTS[column])]=mul_tower_basis(c1[column],column&3);}for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS{coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])]=mul_tower_basis(mask_only_c1[column],column&3);}let prepared_linear=PreparedQm31Multiplier::new(linear);let mut shared=coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev(){shared=prepared_linear.mul(shared).add(coefficients[exponent]);}shared.add(QM31::ONE.add(mask_power_26(explicit_linear)).mul(explicit_g),)}''','MaskRootEq.reference; FillLoopsEq.c1/mask; OwnedMaskHornerEq.source',
 'Linears call; fixed 27-element zero array; both exact source-range fills retain every store; new prepared multiplier; top coefficient read; reverse range multiply then coefficient read and add; explicit power, one addition, multiplication, final shared addition. Index/RHS evaluation reorder in the owned reference is permitted only by proved bounds and pure total reads (FillCellEq.cell), never on arbitrary failing indices.'),
]
records=[]
for marker,expected,law,steps in checks:
 actual=span(src,marker,marker);assert tokens(actual)==tokens(expected),(marker,actual)
 bad=expected[:expected.index('{')]+'{panic!("negative_control")}'
 assert tokens(actual)!=tokens(bad)
 records.append(dict(marker=marker,body=actual,expected_body=expected,law='R1Z.PV_RDCD3_CB_'+law,statement_binding=steps,negative_control='terminal panic replacement rejected, syntactic fail-closed control only'))
constants={'STATE_ONLY_HIDING_C1_COLUMNS':'16','STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS':'10','STATE_ONLY_HIDING_SUMCHECK_ROUNDS':'10','STATE_ONLY_HIDING_FACTOR_DEGREE':'26'}
import re
for name,value in constants.items():assert re.search(r'pub const '+name+r': usize = '+value+r';',src),name
for name,values in [('FACTOR_EXPONENTS',[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25]),('MASK_ONLY_FACTOR_EXPONENTS',[1,3,5,7,9,11,15,17,19,21])]:
 m=re.search(r'const '+name+r':[^=]+=\s*(\[[^]]+\]);',src);assert m,name
 assert tokens(m[1])==tokens(str(values)),name
j=dict(source_path=str(p),source_sha256=sha(p.read_bytes()),records=records,constants=constants,scope='Application bodies only; complete field and deployed-library bindings plus all successful proofs required before row credit',writeback='Both array stores become Array.update, and every returned array is threaded through the next iteration. No mutable-borrow backward result discarded.',drop='Concrete M31/CM31/QM31 and arrays are Copy with no user Drop; fixed stack data only. Primitive memory/layout/drop erasure remains V370.',composition='Existing Aeneas/compiler semantic trust retained; no endpoint premise removal')
(D/'v217-application-source-result.json').write_text(json.dumps(j,indent=2)+'\n');print('Six complete selected-mask application bodies and fixed schedules matched')
