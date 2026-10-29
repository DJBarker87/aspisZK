"""Complete reached application field bodies, with deployed feature selection.
Patterns bind the owned ANF definitions; no theorem about machine code is claimed.
"""
from pathlib import Path
import json,runpy,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
a=runpy.run_path(str(D/'range-source.py'));span,tokens,sha=(a[k] for k in ['span','tokens','sha'])
f=S/'crates/aspis-core/src/field.rs';ct=S/'crates/aspis-core/src/field/ct.rs'
features=json.load(open(D/'deployed-client-features.json'))
core=[x for x in features if x['name']=='aspis-core'];assert core
assert all('ct-host-prover' in x['features'] and not {'r0-op-count','r0-r91-audit','r0-e4-reference'}.intersection(x['features']) for x in core)
assert all(not x['profile']['overflow_checks'] and not x['profile']['debug_assertions'] for x in features)
checks=[]
def add(p,context,marker,expected,model,steps):checks.append((p,context,marker,expected,model,steps))
for name,body,steps in [
 ('subtract_p','pub fn subtract_p(x:u32)->u32{let mask=0u32.wrapping_sub((x>=P)as u32);x.wrapping_sub(P&mask)}','Compare x>=P; bool cast; wrapping zero-minus-bit; bitwise P mask; wrapping subtraction.'),
 ('reduce64','pub fn reduce64(x:u64)->u32{let x=(x&P as u64)+(x>>31);let x=(x&P as u64)+(x>>31);subtract_p(x as u32)}','Two ordered mask/shift/add folds; truncating cast; subtract_p. Release additions use wrapping carrier.'),
 ('add','pub fn add(a:u32,b:u32)->u32{subtract_p(a.wrapping_add(b))}','Wrapping add then subtract_p.'),
 ('sub','pub fn sub(a:u32,b:u32)->u32{subtract_p(a.wrapping_add(P).wrapping_sub(b))}','Wrapping add P, wrapping subtract b, then subtract_p.'),
 ('neg','pub fn neg(a:u32)->u32{let mask=0u32.wrapping_sub((a!=0)as u32);P.wrapping_sub(a)&mask}','Nonzero comparison and bool cast, mask subtraction, P-a wrapping subtraction, bitwise and.')]:
 add(ct,'pub fn '+name+'(','pub fn '+name+'(',body,'ct.'+name,steps)
ctx='#[cfg(feature = "ct-host-prover")]\nimpl M31 {'
for name,body in [('add','pub fn add(self,rhs:Self)->Self{Self(ct::add(self.0,rhs.0))}'),('sub','pub fn sub(self,rhs:Self)->Self{Self(ct::sub(self.0,rhs.0))}'),('neg','pub fn neg(self)->Self{Self(ct::neg(self.0))}')]:
 add(f,ctx,'pub fn '+name+'(',body,'M31.'+name,'Call selected ct helper with raw representatives, then Copy newtype construction.')
add(f,'fn reduce_u64(x: u64) -> u32 { ct::reduce64(x) }','fn reduce_u64(', 'fn reduce_u64(x:u64)->u32{ct::reduce64(x)}','reduce_u64','ct-host-prover selects this definition; audit/reference/default body inactive.')
ctx='impl M31 {\n    pub const ZERO'
for name,body,steps in [
 ('mul','pub fn mul(self,rhs:M31)->M31{M31(reduce_u64(self.0 as u64*rhs.0 as u64))}','Widen both operands; release u64 multiplication; reduce; newtype.'),
 ('reduce_u64','pub fn reduce_u64(value:u64)->M31{M31(reduce_u64(value))}','Call selected reducer; newtype.'),
 ('double','pub fn double(self)->M31{self.add(self)}','Call selected ct add on identical operands.')]:
 add(f,ctx,'pub fn '+name+'(',body,'M31.'+name,steps)
ctx='impl CM31 {\n    pub const ZERO'
for name,body,steps in [
 ('new','pub fn new(a:M31,b:M31)->CM31{CM31{a,b}}','Construct ordered pair.'),
 ('add','pub fn add(self,rhs:CM31)->CM31{CM31{a:self.a.add(rhs.a),b:self.b.add(rhs.b),}}','Ordered a then b ct additions.'),
 ('sub','pub fn sub(self,rhs:CM31)->CM31{CM31{a:self.a.sub(rhs.a),b:self.b.sub(rhs.b),}}','Ordered a then b ct subtractions.'),
 ('mul','pub fn mul(self,rhs:CM31)->CM31{let m0=self.a.mul(rhs.a);let m1=self.b.mul(rhs.b);let m2=M31::reduce_u64((u64::from(self.a.0)+u64::from(self.b.0))*(u64::from(rhs.a.0)+u64::from(rhs.b.0)),);CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1),}}','m0 then m1; left/right raw widening sums, release product, reduction; a subtraction then two b subtractions.'),
 ('square','pub fn square(self)->CM31{CM31{a:M31::reduce_u64((u64::from(self.a.0)+u64::from(self.b.0))*(u64::from(self.a.0)+u64::from(P)-u64::from(self.b.0)),),b:self.a.mul(self.b).double(),}}','Widening, sums/subtraction/product with release wrap semantics; reduce a; multiply then double b.'),
 ('mul_m31','pub fn mul_m31(self,rhs:M31)->CM31{CM31{a:self.a.mul(rhs),b:self.b.mul(rhs),}}','Ordered scalar products.'),
 ('double','pub fn double(self)->CM31{self.add(self)}','Pair addition with itself.')]:
 add(f,ctx,'pub fn '+name+'(',body,'CM31.'+name,steps)
add(f,'fn mul_by_r(','fn mul_by_r(','fn mul_by_r(x:CM31)->CM31{CM31{a:x.a.double().sub(x.b),b:x.a.add(x.b.double()),}}','mul_by_r','Double a then subtract b; double b then add a; construct pair.')
ctx='impl QM31 {\n    pub const ZERO'
for name,body,steps in [
 ('add','pub fn add(self,rhs:QM31)->QM31{QM31{c0:self.c0.add(rhs.c0),c1:self.c1.add(rhs.c1),}}','c0 then c1 pair additions.'),
 ('mul','pub fn mul(self,rhs:QM31)->QM31{let m0=self.c0.mul(rhs.c0);let m1=self.c1.mul(rhs.c1);let m2=self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));QM31{c0:m0.add(mul_by_r(m1)),c1:m2.sub(m0).sub(m1),}}','m0,m1; left/right sums then m2; mul_by_r then c0 add; ordered two c1 subtractions.'),
 ('square','pub fn square(self)->QM31{let c0_square=self.c0.square();let c1_square=self.c1.square();QM31{c0:c0_square.add(mul_by_r(c1_square)),c1:self.c0.mul(self.c1).double(),}}','Two squares; mul_by_r and c0 add; c0*c1 and double.'),
 ('mul_m31','pub fn mul_m31(self,rhs:M31)->QM31{QM31{c0:self.c0.mul_m31(rhs),c1:self.c1.mul_m31(rhs),}}','c0 then c1 scalar products.')]:
 add(f,ctx,'pub fn '+name+'(',body,'QM31.'+name,steps)
ctx='impl PreparedQm31Multiplier {'
add(f,ctx,'pub fn new(','''pub fn new(value:QM31)->Self{let prepare=|component:CM31|[component.a,component.b,component.a.add(component.b)];Self{components:[prepare(value.c0),prepare(value.c1),prepare(value.c0.add(value.c1)),],}}''','PreparedQm31Multiplier.new','prepare closure reads a,b and computes add. Calls on c0,c1, then pair sum. Closure and 3x3 arrays are explicit in model; unit closure holds no capture.')
add(f,ctx,'pub fn mul(','''pub fn mul(self,rhs:QM31)->QM31{let multiply=|left:[M31;3],right:CM31|{let m0=left[0].mul(right.a);let m1=left[1].mul(right.b);let m2=left[2].mul(right.a.add(right.b));CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1),}};let m0=multiply(self.components[0],rhs.c0);let m1=multiply(self.components[1],rhs.c1);let m2=multiply(self.components[2],rhs.c0.add(rhs.c1));QM31{c0:m0.add(mul_by_r(m1)),c1:m2.sub(m0).sub(m1),}}''','PreparedQm31Multiplier.mul','multiply closure preserves reads0,1,2 and all ordered operations. Outer closure calls read components0,1,2 then pair sums. Unit closure has no capture; all constant indices have type-level bounds3. No mutable writes or backward continuation.')
# Fixed constants and Copy representation are part of the binding, not an inferred purity claim.
raw=f.read_text()
assert 'pub const P: u32 = 0x7fff_ffff;' in raw
for declaration in ['pub struct M31(pub u32);','pub struct CM31 {','pub struct QM31 {','pub struct PreparedQm31Multiplier {']:
 i=raw.index(declaration);prefix=raw[max(0,i-90):i]
 assert re.search(r'#\[derive\([^]]*\bCopy\b[^]]*\)\]\s*$',prefix),declaration
for constant,expected in [
 ('pub const ZERO: QM31','pub const ZERO:QM31=QM31{c0:CM31{a:M31(0),b:M31(0),},c1:CM31{a:M31(0),b:M31(0),},}'),
 ('pub const ONE: QM31','pub const ONE:QM31=QM31{c0:CM31{a:M31(1),b:M31(0),},c1:CM31{a:M31(0),b:M31(0),},}')]:
 assert tokens(span(raw,constant,constant))==tokens(expected),constant
records=[]
for p,context,marker,expected,model,steps in checks:
 actual=span(p.read_text(),context,marker)
 # This EXACT inactive cfg statement is the only removed body text. Record it.
 pattern=r'#\[cfg\(feature = "r0-op-count"\)\]\s*let _count = crate::r0_op_count::enter\(crate::r0_op_count::Op::\w+\);'
 removed=re.findall(pattern,actual)
 selected=re.sub(pattern,'',actual)
 assert tokens(selected)==tokens(expected),(model,selected)
 assert tokens(selected)!=tokens(expected[:expected.index('{')]+'{panic!("negative_control")}')
 records.append(dict(path=str(p),source_sha256=sha(p.read_bytes()),context=context,body=actual,selected_body=selected,expected_body=expected,inactive_op_count=removed,model='R1Z.PV_RDCD3_FieldSource.aspis_core.field.'+model,statement_binding=steps))
source=D/'lean-sources/R1Z/PV_RDCD3_FieldSource.lean';lean=source.read_text()
assert sha(source.read_bytes())=='f2b0d2e87275e882e777e9a84b6737e251f607ff3315c4177e378c6f9e281afc'
for r in records:assert r['model'].split('FieldSource.')[1] in lean,r['model']
j=dict(records=records,feature_graph_sha256=sha((D/'deployed-client-features.json').read_bytes()),owned_model_sha256=sha(source.read_bytes()),qualification='Source-pattern to explicitly named ANF model association at existing arithmetic/memory primitive boundary; full row proof and primitive library bindings required. No machine-code/world/observer theorem.',constants='P=2147483647; M31 ZERO/ONE=0/1; CM31/QM31 constants ordered as source, validated separately by model source and closing theorem.',drop='All reached field and Prepared records derive Copy; closure captures are empty; no user destructor. Primitive stack construction/layout remains V370.',composition='Aeneas/compiler semantic trust retained, reclassification only')
(D/'v217-field-source-result.json').write_text(json.dumps(j,indent=2)+'\n');print(len(records),'complete reached field bodies matched after exact inactive op-count removal')
