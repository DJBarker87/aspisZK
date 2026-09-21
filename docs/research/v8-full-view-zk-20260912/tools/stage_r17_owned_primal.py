#!/usr/bin/env python3
"""Reuse final buffers without replacing the baseline affine arithmetic."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
path=root/'r17_owned_primal.rs';path.write_bytes(Path(__file__).with_name(path.name).read_bytes())
meta['owned_primal_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
meta['owned_primal']={}
for name,expected in [('r17_host_relation.rs',meta['baseline_reuse']['r17_host_relation.rs']['after_sha256']),
    ('r17_baseline_reuse_check.rs',meta['baseline_reuse_files']['r17_baseline_reuse_check.rs'])]:
    path=root/name;before=path.read_bytes()
    assert hashlib.sha256(before).hexdigest()==expected
    s=before.decode()
    if name=='r17_host_relation.rs':
        s=one_replace(s,'use super::*;','use super::*;\n#[path="r17_owned_primal.rs"] mod owned_primal;','owned primal module')
        s=one_replace(s,'            finals[c] = primal(&finals[c], a);',
            '            finals[c] = owned_primal::fold(core::mem::take(&mut finals[c]), a);','move each final buffer')
    else:
        s=one_replace(s,'const Q:usize=22;','#[path="r17_owned_primal.rs"] mod owned_primal;\nconst Q:usize=22;','owned helper gate')
        s=one_replace(s,'    for case in 0..256usize {','''    for n in [0usize,1,2,3,4,5,15,16,17,63,64,65,255,256,257] {
        for case in 0..16u32 {
            let alpha=if case==0 {K::ZERO} else if case==1 {K::ONE} else {sample(case+100)};
            let input:Vec<_>=(0..n).map(|i|if case==2 {
                let m=M31(P-1);K{c0:CM31::new(m,m),c1:CM31::new(m,m)}
            } else {sample(case*1024+i as u32)}).collect();
            let expected=affine_primal::fold(&input,alpha);
            let ptr=input.as_ptr();let cap=input.capacity();
            let actual=owned_primal::fold(input,alpha);
            assert_eq!(actual,expected);assert_eq!(actual.as_ptr(),ptr);assert_eq!(actual.capacity(),cap);
        }
    }
    println!("PASS: 240 owned affine folds equal baseline, including incomplete chunks/max limbs; allocation pointer/capacity retained");
    for case in 0..256usize {''','same arithmetic and retained allocation')
    path.write_text(s)
    meta['owned_primal'][name]={'before_sha256':expected,'after_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
