from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');S=D.parent/'codex-pv-rdb2-20261028/src'
def tokens(s):return re.findall(r'"(?:[^"\\]|\\.)*"|::|=>|\w+|[^\s]',re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S))
def body(s,needle):
 a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if d==0:return s[a:i+1]
w=(S/'crates/aspis-r1-cost-probe/src/weights.rs').read_text();h=(S/'crates/aspis-r1-cost-probe/src/host_weights.rs').read_text();t=(S/'crates/aspis-r1-cost-probe/src/transport.rs').read_text();r=(S/'crates/aspis-core/src/state_only_prefix.rs').read_text()
assert tokens(t[t.index('pub const TAU'):t.index(';',t.index('pub const TAU'))+1])==tokens('pub const TAU:[usize;5]=[3,4,2,0,1];')
orig='''{let points=aspis_core::state_only_prefix::r0::statement_points(alpha);let extra=[alpha[8],alpha[9]];let mut factors=[[[K::ZERO;4];5];5];for k in 0..3 {for d in 0..5 {let a=points[k][9-2*TAU[d]];let b=points[k][8-2*TAU[d]];factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];}}for k in 0..2 {factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];let mut x=double(z[k].x);for d in 1..5 {let y=double(x);factors[3+k][d]=[K::ONE,x,y,x.mul(y)];x=double(y);}}Ok(Self::box_from_parts(variant,factors,points,extra))}'''
assert tokens(body(w,'pub fn new('))==tokens(orig)
expected='{let points=state_only_statement_points(alpha);let extra=[alpha[8],alpha[9]];let mut factors=[[[K::ZERO;4];5];5];'
for k in range(3):
 for d,tau in enumerate([3,4,2,0,1]):
  expected+=f'let a=points[{k}][{9-2*tau}];let b=points[{k}][{8-2*tau}];factors[{k}][{d}]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];'
for k in range(2):
 expected+=f'factors[{3+k}][0]=[K::ONE,z[{k}].y,z[{k}].x,z[{k}].x.mul(z[{k}].y)];let mut x=double(z[{k}].x);'
 for d in range(1,5):expected+=f'let y=double(x);factors[{3+k}][{d}]=[K::ONE,x,y,x.mul(y)];x=double(y);'
expected+='Ok(Weights {variant,factors,points,extra})}'
assert tokens(body(h,'pub fn new('))==tokens(expected)
assert tokens(body(w,'pub fn double('))==tokens(body(h,'fn double('))
assert tokens(body(r,'fn state_only_statement_points('))==tokens('''{let mut successor=*z;let mut carry=QM31::ONE;for coordinate in (0..z.len()).rev(){let bit=z[coordinate];let bit_and_carry=bit.mul(carry);successor[coordinate]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;}let mut absorption=*z;absorption[7]=QM31::ONE.sub(absorption[7]);absorption[6]=QM31::ONE.sub(absorption[6]);[*z,successor,absorption]}''')
expected='{let mut successor=*z;let mut carry=QM31::ONE;'
for i in reversed(range(10)):expected+=f'let bit=z[{i}];let bit_and_carry=bit.mul(carry);successor[{i}]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;'
expected+='let mut absorption=*z;absorption[7]=QM31::ONE.sub(absorption[7]);absorption[6]=QM31::ONE.sub(absorption[6]);[*z,successor,absorption]}'
assert tokens(body(h,'fn state_only_statement_points('))==tokens(expected)
assert tokens(body(r,'pub fn statement_points('))==tokens('{super::state_only_statement_points(alpha)}')
records=[]
for p in ['crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/host_weights.rs','crates/aspis-r1-cost-probe/src/transport.rs','crates/aspis-core/src/state_only_prefix.rs']:
 records.append(dict(path=p,sha256=hashlib.sha256((S/p).read_bytes()).hexdigest()))
j=dict(status='PASS',sources=records,unrolling='all 15 tensor factors, both circle rows and all 10 statement-point writes checked in source order',bounds='fixed arrays: k<3,d<5; tau in 0..4; 3+k<5; coordinate<10; loop increments below usize limit',differences=['loop unrolling at literal finite bounds','host returns owned Weights; shipped boxes same value after the arithmetic'],runtime='one public Layout::new::<Weights>() only after pure constructor; failure abort retained, never rewritten to Rust Error::Allocation',proof='PV_B2_C_ConstructorSuccess.new_eq_staged/new_total in owned imports cohort; PV_RDB2C_Box.complete pending MIR intrinsic association',trust='structural (K-1 substitute); reclassification within existing tool trust; not premise removal')
(D/'constructor-binding.json').write_text(json.dumps(j,indent=2));print(json.dumps(j))
