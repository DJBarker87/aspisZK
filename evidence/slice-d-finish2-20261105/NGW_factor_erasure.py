from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;s=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
need=['let points=aspis_core::state_only_prefix::r0::statement_points(alpha);','let extra=[alpha[8],alpha[9]];','for k in 0..3 { for d in 0..5 {','let a=points[k][9-2*TAU[d]]; let b=points[k][8-2*TAU[d]];','factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];','factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];','let mut x=double(z[k].x);','for d in 1..5 {','let y=double(x); factors[3+k][d]=[K::ONE,x,y,x.mul(y)]; x=double(y);','Ok(Self::box_from_parts(variant, factors, points, extra))']
start=s.index('pub fn new(variant:Variant,alpha:');end=s.index('pub fn raw(',start);body=s[start:end];last=-1
for n in need:i=body.index(n);assert i>last;last=i
x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());h=x['crates/aspis-r1-cost-probe/src/NGW_new.rs'];assert 'static 'not in h and 'static mut'not in h
assert 'product(K::ONE.sub(a),K::ONE.sub(b),log),product(a,K::ONE.sub(b),log),product(K::ONE.sub(a),b,log),product(a,b,log)'in h
assert 'let y=dbl(a,&mut log);let mut out=[K::ONE,a,y,cmul(a,y,&mut log)];a=dbl(y,&mut log);'in h
(E/'NGW_FACTOR_ERASURE.json').write_text(json.dumps(dict(frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(s.encode()).hexdigest(),source_order_verified=need,split='point selection; scalar-pair row; one observed write window; circle scalar step; initial row; exact loop controls',multiplication='opaque local-record reply, paired NGW_ProductLaw.total',double='CLOSED NGM packet, SAME canonical x/y domain still composed in Lean',caller_boundary='canonical alpha[10] and z[2].x/y are NFW producer boundaries',status='source inspection only; complete row remains OPEN'),indent=2)+'\n')
print('new source order checked; no closure inferred')
