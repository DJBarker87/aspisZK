#!/usr/bin/env python3
"""Host-only beta-polynomial correction; keep the former G audit as reference."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==184 and 'r28_affine'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists()and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
path=dst/'docs/research/v8-no-work-100-20260907/experiments/r17_c1_witness_audit.rs';s=path.read_text()
start=s.index('fn r17_g_witness_audit(');end=s.index('// First affine helper step only:',start);old=s[start:end];new=old
def replace(old,newer):
    global new
    assert new.count(old)==1,old;new=new.replace(old,newer)
replace('let mut matrix=vec![vec![K::ZERO;1022];626];','''let r_ordinary=corelib::sumcheck::polynomial_for_extension(rq,&rw);
    let r_cross=corelib::sumcheck::polynomial_for_extension(rq,&gw);
    assert!(r_ordinary.iter().all(|&v|v==K::ZERO),"R28 ordinary polynomial premise");
    let mut matrix=vec![vec![K::ZERO;1022];633];''')
replace('''        matrix[625][j]=dot(&dw,&q);
        let poly=corelib::sumcheck::polynomial_for_extension(&q,&wb).map(|x|beta.mul(x));
        for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){matrix[619+i][j]=poly[k];}''','''        let ordinary=corelib::sumcheck::polynomial_for_extension(&q,&rw);
        let structured=corelib::sumcheck::polynomial_for_extension(&q,&gw);
        for i in 0..7{matrix[619+i][j]=ordinary[i];matrix[626+i][j]=structured[i];}''')
replace('let mut target=vec![K::ZERO;626];','let mut target=vec![K::ZERO;633];')
replace('''    for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){target[619+i]=rp[k].mul(scale.inv()).neg();}
    target[625]=dot(&dw,rq).mul(scale.inv());''','''    for i in 0..7{target[619+i]=r_cross[i].mul(scale.inv()).neg();}''')
replace('for i in 0..626{reduced[i].push(target[i]);}','for i in 0..633{reduced[i].push(target[i]);}')
replace('for i in 0..626{assert_eq!','for i in 0..633{assert_eq!')
replace('let q=qvector(&x,p.abc);let g=map.inverse(&chord(&q,p.abc));','''let q=qvector(&x,p.abc);let g=map.inverse(&chord(&q,p.abc));
    let g_ordinary=corelib::sumcheck::polynomial_for_extension(&q,&rw);
    let g_structured=corelib::sumcheck::polynomial_for_extension(&q,&gw);
    for i in 0..7{
        assert_eq!(r_cross[i].add(scale.mul(g_ordinary[i])),K::ZERO,"beta cross coefficient {i}");
        assert_eq!(g_structured[i],K::ZERO,"beta squared coefficient {i}");
    }''')
replace('R19_G_WITNESS_JOINT equations=626 rank={rank}','R29_G_WITNESS_JOINT equations=633 rank={rank} beta_polynomial_coefficients_zero=true')
s=s[:start]+old.replace('fn r17_g_witness_audit(','fn r19_g_witness_audit_reference(',1)+new+s[end:]
path.write_text(s);m['files'][str(path.relative_to(dst))]=sha(path)
m['r29_beta_uniform']={'control_manifest_sha256':sha(src/'r18-stage.json'),'G_equations':633,'matrix_independent_of_beta':True,'old_G_audit_retained':True,'host_diagnostic_only':True,'verifier_changed':False,'source_challenges_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files']),'verifier_changed':False}))
