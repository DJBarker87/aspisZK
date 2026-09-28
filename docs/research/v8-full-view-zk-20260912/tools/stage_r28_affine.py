#!/usr/bin/env python3
"""Extend the existing opposite-witness diagnostic, never the verifier path."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==184 and 'r28_h1_capacity'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists() and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';path=ex/'r17_c1_witness_audit.rs';s=path.read_text()
cut=s.index('// Literal old/new terminal enumeration');head=s[:cut];tail=s[cut:]
def replace(old,new):
    global head
    assert head.count(old)==1,old;head=head.replace(old,new)
replace('alpha: K, queries:', 'kappa: K, alpha: K, queries:')
replace('let mut matrix = vec![vec![K::ZERO;1022];562];','let wr=crate::opening_weights::quotient_weights(z,kappa,p.abc,p.tau,false);\n    let rq_poly=corelib::sumcheck::polynomial_for_extension(&rq,&wr);\n    let sent=[0,1,2,3,5,6];\n    let mut matrix = vec![vec![K::ZERO;1022];568];')
replace('let f=primal(&q,alpha);for i in 0..256{matrix[306+i][j]=f[i];}', 'let f=primal(&q,alpha);for i in 0..256{matrix[306+i][j]=f[i];}\n        let poly=corelib::sumcheck::polynomial_for_extension(&q,&wr);\n        for i in 0..6{matrix[562+i][j]=poly[sent[i]];}')
replace('let hc=map.forward(h0);let mut target=vec![K::ZERO;562];','let hc=map.forward(h0);let mut target=vec![K::ZERO;568];\n    for i in 0..6{target[562+i]=rq_poly[sent[i]].mul(scale.inv()).neg();}')
replace('for i in 0..562{reduced[i].push(target[i]);}','for i in 0..568{reduced[i].push(target[i]);}')
replace('assert_eq!(pivots.len(),540);','assert_eq!(pivots.len(),545);')
replace('reduced[540..]','reduced[545..]')
replace('for i in 0..562{assert_eq!','for i in 0..568{assert_eq!')
replace('println!("R17_H1_WITNESS_JOINT rank=540 equations=562 compatibility_residuals=22', 'assert!(corelib::sumcheck::polynomial_for_extension(&total,&wr).iter().all(|&v|v==K::ZERO),"ordinary first relation zero after actual H1 correction");\n    println!("R28_H1_WITNESS_JOINT ordinary_first_all7_zero=true rank=545 equations=568 compatibility_residuals=23')
path.write_text(head+tail)
perf=ex/'performance.rs';s=perf.read_text();old='r17_h1_witness_joint_audit(&h1_ood_delta,&delta,&s.z,&p,alpha,&queries,&enc,&decoder)';assert s.count(old)==1
perf.write_text(s.replace(old,'r17_h1_witness_joint_audit(&h1_ood_delta,&delta,&s.z,&p,audit_kappa,alpha,&queries,&enc,&decoder)'))
for f in [path,perf]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r28_affine']={'control_manifest_sha256':sha(src/'r18-stage.json'),'host_diagnostic_only':True,'H1_equations':568,'expected_H1_rank':545,'G_equations_unchanged':626,'G_rank_unchanged':602,'verifier_changed':False,'source_beta_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files']),'verifier_changed':False}))
