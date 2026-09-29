#!/usr/bin/env python3
"""Focused native experiments on the source-pinned R81 scalar-G winner."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--variant',choices=['pair','inline','affine','compose','unroll','dotinline','matrix'],required=True)
a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='befe62a23b9ad254a82ac068ee277790e48c172a12acb324fc0555ab075c6263'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==210
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
if a.variant in ['pair','compose','unroll','dotinline','matrix']:
    ordinary=ex/'r19_channel_ordinary.rs'
    ordinary.write_text(ordinary.read_text()+'\n'+(here/'r62_entry.rs').read_text());changed.append(ordinary)
    scalar=ex/'r22_scalar.rs';v=scalar.read_text()
    assert v.count('entry(factors,0,')==2
    scalar.write_text(v.replace('entry(factors,0,','r62_entry(factors,'));changed.append(scalar)
    native=ex/'r27_native.rs';v=native.read_text();needle='r19_channel_ordinary::r27_tensor_check(x);'
    assert v.count(needle)==1
    native.write_text(v.replace(needle,needle+'r19_channel_ordinary::r62_entry_check(x);'));changed.append(native)
    check=ex/'r27_check.rs';v=check.read_text();needle='    for world in 0..2 {'
    assert v.count(needle)==1
    check.write_text(v.replace(needle,'    println!("R82_PAIR entry_comparisons=262144 changed_primitive=R81_short_dot old_entry_retained=true");\n'+needle));changed.append(check)
if a.variant=='inline':
    # R24's old inline experiment regressed. This tests the newer partial-
    # product kernel and substantially changed callers, not that old binary.
    field=dst/'crates/aspis-core/src/field.rs';v=field.read_text()
    old='''    #[inline(never)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        if let Some(result)=r24_canonical_mul(self,rhs) {return result;}
        let m0 = self.c0.mul(rhs.c0);'''
    new='''    #[inline(always)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        if let Some(result)=r24_canonical_mul(self,rhs) {return result;}
        self.r82_mul_fallback(rhs)
    }
    #[inline(never)]
    fn r82_mul_fallback(self, rhs: QM31) -> QM31 {
        let m0 = self.c0.mul(rhs.c0);'''
    assert v.count(old)==1;field.write_text(v.replace(old,new));changed.append(field)
if a.variant in ['affine','compose','unroll','dotinline','matrix']:
    query=ex/'query_arithmetic.rs';v=query.read_text()
    # Only selected combine_beta; keep the old reference literally unchanged.
    start=v.index('pub(super) fn combine_beta(');end=v.index('// Caller-owned decoded storage',start)
    body=v[start:end]
    old='out[slot]=value.add(corelib::field::qm31_sum_products3_prepared(&powers.helpers,&helpers));'
    new='out[slot]=corelib::field::qm31_add_sum_products3_prepared(value,&powers.helpers,&helpers);'
    assert body.count(old)==1
    query.write_text(v[:start]+body.replace(old,new)+v[end:]);changed.append(query)
if a.variant in ['compose','unroll','dotinline','matrix']:
    scalar=ex/'r22_scalar.rs';v=scalar.read_text()
    old='let mut out=corelib::field::qm31_dot(normal,&values[..16]);'
    new='''let mut out=corelib::field::r25_checked_dot(normal,&values[..16])
        .unwrap_or_else(||corelib::field::qm31_dot(normal,&values[..16]));'''
    assert v.count(old)==1;scalar.write_text(v.replace(old,new));changed.append(scalar)
if a.variant=='unroll':
    basis=ex/'r20_semantic_basis.rs';v=basis.read_text()
    old='''        for degree in 2..=27 {
            powers[degree-1]=if degree%2==0 {let p=powers[degree/2-1];p.mul(p)}
                else {powers[degree-2].mul(q)};
        }'''
    new='\n'.join(f'        powers[{d-1}]=powers[{d//2-1}].mul(powers[{d//2-1}]);'if d%2==0
        else f'        powers[{d-1}]=powers[{d-2}].mul(q);'for d in range(2,28))
    assert v.count(old)==1;basis.write_text(v.replace(old,new));changed.append(basis)
if a.variant=='dotinline':
    dot=dst/'crates/aspis-core/src/r25_checked_dot.rs';v=dot.read_text()
    old='#[inline(never)]\npub fn r25_checked_dot'
    assert v.count(old)==1
    dot.write_text(v.replace(old,'#[inline(always)]\npub fn r25_checked_dot'));changed.append(dot)
if a.variant=='matrix':
    field=dst/'crates/aspis-core/src/field.rs';v=field.read_text()
    old='pub struct PreparedQm31Multiplier {\n    components: [[M31; 3]; 3],\n}'
    new='''pub struct PreparedQm31Multiplier {
    components: [[M31; 3]; 3],
    // Canonical [-b,-d,2c-d,c+2d,-c-2d]; [P;5] marks raw fallback.
    matrix: [M31; 5],
}'''
    assert v.count(old)==1;v=v.replace(old,new)
    old='''                prepare(value.c0.add(value.c1)),
            ],
        }'''
    new='''                prepare(value.c0.add(value.c1)),
            ],
            matrix: if [value.c0.a.0,value.c0.b.0,value.c1.a.0,value.c1.b.0]
                .iter().all(|&v|v<P) {
                let c=value.c1.a;let d=value.c1.b;let y=c.add(d.double());
                [value.c0.b.neg(),d.neg(),c.double().sub(d),y,y.neg()]
            }else{[M31(P);5]},
        }'''
    assert v.count(old)==1;v=v.replace(old,new)
    needle='''        // components are private and constructed only by new(value).
'''
    extra='''        // Four canonical products fit u64. The matrix is constructor-owned;
        // a sentinel rejects noncanonical original values without new panics.
        if self.matrix[0].0<P && [rhs.c0.a.0,rhs.c0.b.0,rhs.c1.a.0,rhs.c1.b.0]
            .iter().all(|&v|v<P) {
            let [e,f,g,h]=[rhs.c0.a.0,rhs.c0.b.0,rhs.c1.a.0,rhs.c1.b.0].map(u64::from);
            let [a,b,c,d]=[self.components[0][0].0,self.components[0][1].0,
                self.components[1][0].0,self.components[1][1].0].map(u64::from);
            let [nb,nd,x,y,ny]=self.matrix.map(|v|u64::from(v.0));
            let dot=|a:u64,b:u64,c:u64,d:u64|M31::reduce_u64((a*e)
                .wrapping_add(b*f).wrapping_add(c*g).wrapping_add(d*h));
            return QM31{c0:CM31::new(dot(a,nb,x,ny),dot(b,a,y,x)),
                c1:CM31::new(dot(c,nd,a,nb),dot(d,c,b,a))};
        }
'''
    assert v.count(needle)==1;field.write_text(v.replace(needle,extra+needle));changed.append(field)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
assert len(m['files'])==210
m['r82_native']={'control_manifest_sha256':sha(src/'r18-stage.json'),'variant':a.variant,
    'protocol_changed':False,'validation_removed':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'variant':a.variant}))
