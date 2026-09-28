#!/usr/bin/env python3
"""Inline the canonical path only; preserve and outline the original fallback."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==183 and 'r24_prepared' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';text=field.read_text()
body='''        let m0 = self.c0.mul(rhs.c0);
        let m1 = self.c1.mul(rhs.c1);
        let m2 = self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));
        QM31 {
            c0: m0.add(mul_by_r(m1)),
            c1: m2.sub(m0).sub(m1),
        }'''
old='''    #[inline(never)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        if let Some(result)=r24_canonical_mul(self,rhs) {return result;}
'''+body+'\n    }'
new='''    #[inline(always)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        if let Some(result)=r24_canonical_mul(self,rhs) {return result;}
        r24_noncanonical_mul(self,rhs)
    }'''
assert text.count(old)==1;field.write_text(text.replace(old,new))
helper=field.parent/'r24_guarded_qm.rs'
helper.write_text(helper.read_text()+'\n#[cold] #[inline(never)]\nfn r24_noncanonical_mul(left:QM31,rhs:QM31)->QM31 {\n'+body.replace('self.','left.')+'\n}\n')
for path in [field,helper]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_inline']={'control_manifest_sha256':sha(src/'r18-stage.json'),'canonical_fast_path_inline':True,'original_fallback_cold_outlined':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
