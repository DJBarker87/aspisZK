#!/usr/bin/env python3
"""Specialize actual canonical squares; retain public raw-input fallbacks."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='17ab8a660db4eca296609b6b38028a30537069c45f93ad5afa88d0d8c757d808'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='5923dd9419cda40ff1274bca67823f6e0b579c1270b86d5e3fb2c3da0fc3a613'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';core=dst/'crates/aspis-core/src';changed=[]
for folder in [ex,core]:
    f=folder/'r96_raw_square.rs';shutil.copy2(here/f.name,f);changed.append(f)
f=core/'field.rs';s=f.read_text();old='        if let Some(result)=r24_canonical_mul(self,self) {return result;}'
assert s.count(old)==1
s=s.replace(old,'''        let limbs=[self.c0.a.0,self.c0.b.0,self.c1.a.0,self.c1.b.0];
        if limbs.iter().all(|&v|v<P) {
            let r=r96_raw_square(limbs).map(M31::reduce_u64);
            return QM31{c0:CM31::new(r[0],r[1]),c1:CM31::new(r[2],r[3])};
        }''')
f.write_text(s+'\ninclude!("r96_raw_square.rs");\n');changed.append(f)
f=ex/'r81_canonical_basis.rs';s=f.read_text();old='pub fn square(self)->Self {self.mul(self)}';assert s.count(old)==1
f.write_text(s.replace(old,'pub fn square(self)->Self {Self(r96_raw_square(self.0).map(reduce))}')+'\ninclude!("r96_raw_square.rs");\n');changed.append(f)
f=ex/'r20_semantic_basis.rs';s=f.read_text();old='let p=powers[degree/2-1];p.mul(p)';assert s.count(old)==1
f.write_text(s.replace(old,'let p=powers[degree/2-1];p.square()'));changed.append(f)
f=ex/'r96_square_check.rs';shutil.copy2(here/f.name,f);changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r96-square-check"\npath="../r96_square_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r96_square']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
