"""Bind the fixed traversal proof to exact frozen Rust control shapes.
This is a structural check, not a substitute for the open native field/helper link.
"""
from pathlib import Path
import re,json,hashlib
R=Path.cwd();D=Path(__file__).resolve().parent
old=R/'crates/aspis-core/src/state_only_hiding.rs';copy=R/'crates/aspis-prover/src/host_arithmetic.rs'
def body(p,name):
 s=p.read_text();start=s.index('fn '+name+'(');a=s.index('{',start);depth=1;i=a+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def tokens(s):return re.findall(r'\w+|[^\w\s]',re.sub(r'//[^\n]*','',s))
def equal(name,actual,expected):assert tokens(actual)==tokens(expected),name
selected='let mut coefficients = [QM31::ZERO; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];\n'
selected+='\n'.join(f'coefficients[FACTOR_EXPONENTS[{i}] as usize] = mul_tower_basis(c1[{i}], {i}&3);' for i in range(16))+'\ncoefficients'
equal('selected_coefficients',body(copy,'selected_coefficients'),selected)
mask='\n'.join(f'coefficients[MASK_ONLY_FACTOR_EXPONENTS[{i}] as usize] = mul_tower_basis(mask_only_c1[{i}], {i}&3);'for i in range(10))+'\ncoefficients'
equal('mask_only_coefficients',body(copy,'mask_only_coefficients'),mask)
horner='let prepared_linear = PreparedQm31Multiplier::new(linear);\nlet mut shared = coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];\n'
horner+='\n'.join(f'shared = prepared_linear.mul(shared).add(coefficients[{i}]);'for i in reversed(range(26)))+'\nshared'
equal('selected_horner',body(copy,'selected_horner'),horner)
original='''
let (linear, explicit_linear) = selected_mask_linears(point);
let mut coefficients = [QM31::ZERO; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
 coefficients[usize::from(FACTOR_EXPONENTS[column])] = mul_tower_basis(c1[column], column & 3);
}
for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
 coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] = mul_tower_basis(mask_only_c1[column], column & 3);
}
let prepared_linear = PreparedQm31Multiplier::new(linear);
let mut shared = coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];
for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {
 shared = prepared_linear.mul(shared).add(coefficients[exponent]);
}
shared.add(QM31::ONE.add(mask_power_26(explicit_linear)).mul(explicit_g),)
'''
equal('original selected mask root',body(old,'state_only_selected_mask_value'),original)
r={'original_path':str(old.relative_to(R)),'copy_path':str(copy.relative_to(R)),
 'original_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'copy_sha256':hashlib.sha256(copy.read_bytes()).hexdigest(),
 'control_shapes_checked':['original selected mask root','selected_coefficients (16)','mask_only_coefficients (10)','selected_horner (26 descending)'],
 'result':'all exact Rust token shapes match','scope':'control-shape validation only; universal original/copy field/helper transport and row law remain open',
 'source_changed':False}
(D/'d324-range117-source-check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
