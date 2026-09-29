#!/usr/bin/env python3
"""Compose unreduced complex Karatsuba pairs with the retained raw bounds."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='fc8723321e919f51abdf4b0ab9d4d60ea84c66afc2a94869f35406827df44f9a'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='5ff291f6956eb58653a3fceea8b0e9e5f51de2088593ce1fe78763b5f26d0e17'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';core=dst/'crates/aspis-core/src';changed=[]
for folder in [ex,core]:
    f=folder/'r94_raw.rs';shutil.copy2(here/f.name,f);changed.append(f)
f=core/'field.rs';f.write_text(f.read_text()+'\ninclude!("r94_raw.rs");\n');changed.append(f)
f=core/'r24_guarded_qm.rs';f.write_text('''// Preserve every canonical guard and the caller's raw-input fallback.
#[inline(always)]
fn r24_canonical_mul(left:QM31,right:QM31)->Option<QM31> {
    let x=[left.c0.a.0,left.c0.b.0,left.c1.a.0,left.c1.b.0];
    let y=[right.c0.a.0,right.c0.b.0,right.c1.a.0,right.c1.b.0];
    if x.iter().chain(y.iter()).any(|&v|v>=P) {return None;}
    let out=r94_raw(x,y).map(M31::reduce_u64);
    Some(QM31{c0:CM31::new(out[0],out[1]),c1:CM31::new(out[2],out[3])})
}
''');changed.append(f)
f=core/'r25_checked_dot.rs';s=f.read_text();start=s.index('    let [a,b,c,d]=x.map(u64::from);');end=s.index('\n}\n',start)
s=s[:start]+'    Some(r94_raw(x,y))'+s[end:];f.write_text(s);changed.append(f)
f=ex/'r81_canonical_basis.rs';s=f.read_text()
for sig,body in [('    #[inline(always)] pub fn mul(self,rhs:Self)->Self {','        Self(self.raw(rhs).map(reduce))'),
                 ('    fn raw(self,rhs:Self)->[u64;4] {','        r94_raw(self.0,rhs.0)')]:
    assert s.count(sig)==1;start=s.index(sig)+len(sig);end=s.index('\n    }',start)
    s=s[:start]+'\n'+body+s[end:]
f.write_text(s+'\ninclude!("r94_raw.rs");\n');changed.append(f)
f=ex/'r94_product_check.rs';shutil.copy2(here/f.name,f);changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r94-product-check"\npath="../r94_product_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r94_products']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
