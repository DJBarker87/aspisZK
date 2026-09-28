#!/usr/bin/env python3
"""Reuse guarded product at the prepared multiplier boundary; keep fallback."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==183 and 'r24_qm' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';text=field.read_text()
old='''    #[inline(always)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        let multiply = |left: [M31; 3], right: CM31| {'''
new='''    #[inline(never)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        // components are private and constructed only by new(value).
        let value=QM31{c0:CM31::new(self.components[0][0],self.components[0][1]),
            c1:CM31::new(self.components[1][0],self.components[1][1])};
        if let Some(result)=r24_canonical_mul(value,rhs) {return result;}
        let multiply = |left: [M31; 3], right: CM31| {'''
assert text.count(old)==1;field.write_text(text.replace(old,new))
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r23_field_check.rs';text=test.read_text()
old='[(a.mul(b),ar.mul(br)),(a.square(),ar.square())]';assert text.count(old)==1
text=text.replace(old,'[(a.mul(b),ar.mul(br)),(a.square(),ar.square()),(aspis_core::field::PreparedQm31Multiplier::new(a).mul(b),r23_reference_field::PreparedQm31Multiplier::new(ar).mul(br))]').replace('operations_per_pair=2','operations_per_pair=3')
old='let actual=std::panic::catch_unwind(|| {let mut v=[0;16];a.mul(b).write_le_bytes(&mut v);v});'
new=old+'''
        let prepared_original=std::panic::catch_unwind(|| {let mut v=[0;16];r23_reference_field::PreparedQm31Multiplier::new(mk(&l[..4])).mul(mk(&l[4..])).write_le_bytes(&mut v);v});
        let prepared_actual=std::panic::catch_unwind(|| {let mut v=[0;16];aspis_core::field::PreparedQm31Multiplier::new(a).mul(b).write_le_bytes(&mut v);v});
        match(prepared_original,prepared_actual){(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("prepared raw outcome changed")}
'''
assert text.count(old)==1;text=text.replace(old,new)
test.write_text(text)
for path in [field,test]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_prepared']={'control_manifest_sha256':sha(src/'r18-stage.json'),'original_fallback':True,'source_invariant':'private components constructed only by new(value)','outlined':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
