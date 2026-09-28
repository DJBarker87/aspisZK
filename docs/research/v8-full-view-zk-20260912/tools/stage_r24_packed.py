#!/usr/bin/env python3
"""Exact two-lane QM31 add/sub; original arbitrary-constructor path retained."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==183 and 'r24_qm' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';text=field.read_text()
for op,flag in [('add','false'),('sub','true')]:
    old=f'pub fn {op}(self, rhs: QM31) -> QM31 {{'
    assert text.count(old)==1;text=text.replace(old,old+f'\n        if let Some(result)=r24_packed_pair(self,rhs,{flag}) {{return result;}}')
field.write_text(text)
helper=field.parent/'r24_guarded_qm.rs';helper.write_text(helper.read_text()+'\n'+(here/'r24_packed_addsub.rs').read_text())
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r23_field_check.rs';text=test.read_text()
old='[(a.mul(b),ar.mul(br)),(a.square(),ar.square())]';assert text.count(old)==1
text=text.replace(old,'[(a.mul(b),ar.mul(br)),(a.square(),ar.square()),(a.add(b),ar.add(br)),(a.sub(b),ar.sub(br))]').replace('operations_per_pair=2','operations_per_pair=4')
at='    std::panic::set_hook(hook);'
extra='''    let raw=[0,1,P-1,P,P+1,u32::MAX/2+2,u32::MAX-1,u32::MAX];
    let mk=|v:[u32;4]|K{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))};
    let mr=|v:[u32;4]|R{c0:r23_reference_field::CM31::new(r23_reference_field::M31(v[0]),r23_reference_field::M31(v[1])),c1:r23_reference_field::CM31::new(r23_reference_field::M31(v[2]),r23_reference_field::M31(v[3]))};
    for lane in 0..4 {for x in raw {for y in raw {for sub in [false,true] {
        let mut a=[P-1,P,0,1];let mut b=[P,0,1,P-1];a[lane]=x;b[lane]=y;
        let original=std::panic::catch_unwind(|| {let mut bytes=[0;16];let (a,b)=(mr(a),mr(b));(if sub{a.sub(b)}else{a.add(b)}).write_le_bytes(&mut bytes);bytes});
        let actual=std::panic::catch_unwind(|| {let mut bytes=[0;16];let (a,b)=(mk(a),mk(b));(if sub{a.sub(b)}else{a.add(b)}).write_le_bytes(&mut bytes);bytes});
        match (original,actual) {(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("packed outcome changed")}
    }}}}
    println!("R24_PACKED raw_boundary_cases=512 original_panic_behavior_retained=true");
'''
assert text.count(at)==1;test.write_text(text.replace(at,extra+at))
for path in [field,helper,test]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_packed']={'control_manifest_sha256':sha(src/'r18-stage.json'),'original_fallback':True,'inclusive_lane_bound':2147483647,'helper_sha256':sha(here/'r24_packed_addsub.rs')}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
