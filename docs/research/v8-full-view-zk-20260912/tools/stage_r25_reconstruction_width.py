#!/usr/bin/env python3
"""Eliminate checked wide constant products after canonical channel reduction."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==180 and 'r25_checked_dot'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists() and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';s=field.read_text()
start=s.index('fn qm31_from_karatsuba_channel_sums(');end=s.index('\n}',start)+2;old=s[start:end];new=old
for old_expr,new_expr in [('3*d','d.wrapping_add(d).wrapping_add(d)'),('2*f','f.wrapping_add(f)'),('3*e','e.wrapping_add(e).wrapping_add(e)')]:
    assert new.count(old_expr)==1;new=new.replace(old_expr,new_expr)
field.write_text(s[:start]+new+s[end:])
test=dst/'docs/research/v8-no-work-100-20260907/experiments/r24_dot_check.rs';s=test.read_text();marker='    let lengths='
assert s.count(marker)==1
check='''    let mut small_cases=0;
    for trial in 0..200064 {
        let mut a=[sample(),sample(),sample(),sample()];let mut b=[sample(),sample(),sample(),sample()];
        if trial<64 {let v=M31([0,1,2,P-2,P-1][trial%5]);a.fill(K{c0:CM31::new(v,v),c1:CM31::new(v,v)});if trial%2==0{b=a;}}
        let mut expected=K::ZERO;
        for n in 0..4 {expected=expected.add(a[n].mul(b[n]));let actual=match n{
            1=>Some(aspis_core::field::qm31_sum_products2([a[0],a[1]],[b[0],b[1]])),
            2=>Some(aspis_core::field::qm31_sum_products3([a[0],a[1],a[2]],[b[0],b[1],b[2]])),
            3=>Some(aspis_core::field::qm31_sum_products4(a,b)),_=>None};
            if let Some(x)=actual{assert_eq!(x,expected);small_cases+=1;}
        }
    }
    println!("R25_SMALL_DOT cases={small_cases} canonical_vectors=200064 arities=2,3,4");
'''
test.write_text(s.replace(marker,check+marker))
for path in [field,test]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r25_reconstruction_width']={'control_manifest_sha256':sha(src/'r18-stage.json'),'sites':3,'premise':'each operand is output of unchanged canonical reducer, hence below P; sums below 3P','global_overflow_checks':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
