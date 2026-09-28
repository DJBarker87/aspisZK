#!/usr/bin/env python3
"""Guarded canonical QM31 multiplication, separate from the add/sub experiment."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--outlined',action='store_true');p.add_argument('--split-scalar',action='store_true');a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==182
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';text=field.read_text()
old='''pub fn mul(self, rhs: QM31) -> QM31 {
        let m0 = self.c0.mul(rhs.c0);'''
new='''pub fn mul(self, rhs: QM31) -> QM31 {
        if let Some(result)=r24_canonical_mul(self,rhs) {return result;}
        let m0 = self.c0.mul(rhs.c0);'''
assert text.count(old)==1;text=text.replace(old,new)
if a.outlined:
    old='''#[inline(always)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        if let Some(result)=r24_canonical_mul(self,rhs) {return result;}'''
    assert text.count(old)==1;text=text.replace(old,old.replace('#[inline(always)]','#[inline(never)]'))
field.write_text(text+'\ninclude!("r24_guarded_qm.rs");\n')
helper=field.parent/'r24_guarded_qm.rs';shutil.copy2(here/helper.name,helper)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r23_field_check.rs';text=test.read_text();at='    std::panic::set_hook(hook);'
extra='''    for limb in 0..8 {for bad in [P,P+1,u32::MAX] {
        let mut l=[1u32;8];l[limb]=bad;
        let bytes=|v:&[u32]| {let mut b=[0u8;16];for (i,x) in v.iter().enumerate(){b[4*i..4*i+4].copy_from_slice(&x.to_le_bytes());}b};
        let a=K{c0:CM31::new(M31(l[0]),M31(l[1])),c1:CM31::new(M31(l[2]),M31(l[3]))};
        let b=K{c0:CM31::new(M31(l[4]),M31(l[5])),c1:CM31::new(M31(l[6]),M31(l[7]))};
        let mk=|v:&[u32]|r23_reference_field::QM31{c0:r23_reference_field::CM31::new(r23_reference_field::M31(v[0]),r23_reference_field::M31(v[1])),c1:r23_reference_field::CM31::new(r23_reference_field::M31(v[2]),r23_reference_field::M31(v[3]))};
        let original=std::panic::catch_unwind(|| {let mut v=[0;16];mk(&l[..4]).mul(mk(&l[4..])).write_le_bytes(&mut v);v});
        let actual=std::panic::catch_unwind(|| {let mut v=[0;16];a.mul(b).write_le_bytes(&mut v);v});
        match (original,actual) {(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("invalid constructor outcome changed")}
        let _=bytes;
    }}
    println!("R24_QM invalid_constructor_cases=24 old_fallback_retained=true");
'''
assert text.count(at)==1;test.write_text(text.replace(at,extra+at))
changed=[field,helper,test]
if a.split_scalar:
    for name,needles in [('r22_scalar.rs',['pub(super) fn terminal_scalar(']),('r19_channel_ordinary.rs',['fn prepare_rows_scalar(','fn block_terminal_scalar_impl('])]:
        path=ex/name;text=path.read_text()
        for needle in needles:
            assert text.count(needle)==1;text=text.replace(needle,'#[inline(never)]\n'+needle)
        path.write_text(text);changed.append(path)
for path in changed:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_qm']={'control_manifest_sha256':sha(src/'r18-stage.json'),'canonical_guard':True,'original_fallback':True,'outlined':a.outlined,'split_scalar':a.split_scalar}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
