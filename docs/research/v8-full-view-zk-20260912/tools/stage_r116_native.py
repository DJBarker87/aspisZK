#!/usr/bin/env python3
"""Fuse the known single query component; retain identical transcript chronology."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='c05fa38791ad84eb3f22ebda07586fb8ef1fd0f0cc56a6ef2c559c7b9b67b41f'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def save(n,s):
    f=ex/n;f.write_text(s);changed.append(f)
for n in ['r116_mixed.rs','r116_query.rs']:save(n,(here/n).read_text())
f=ex/'r81_canonical_basis.rs';save(f.name,f.read_text()+'\ninclude!("r116_mixed.rs");\n')
f=ex/'r17_host_relation.rs';s=f.read_text()
for old,new in [
 ('    let mut query=WeightAccumulator::empty(8);','    let mut query=r116_query::Query::new();'),
 ('}else{inject(&mut query,&mut claim,&values,&xs,rho)?};','}else{query.inject(&mut claim,&values,&xs,rho)?};'),
 ('if reference{dense=fold_dense(&dense,a)}else{query.fold_deferred_relation_arity4(a)}','if reference{dense=fold_dense(&dense,a)}'),
 ('''    let mut terminal=corelib::field::qm31_sum_products4(
        if reference {core::array::from_fn(|i|dense[i])}else{query.weight_prefix::<4>()},
        core::array::from_fn(|i|finals[i]));''','''    // Query weights are not consumed by any intervening transcript operation.
    // Only this deterministic arithmetic is deferred; inc is absorbed unchanged.
    let mut terminal=if reference {corelib::field::qm31_sum_products4(
        core::array::from_fn(|i|dense[i]),core::array::from_fn(|i|finals[i]))
    }else{query.terminal([alphas[1],alphas[2],alphas[3]],core::array::from_fn(|i|finals[i]))};''')]:
    assert s.count(old)==1,old;s=s.replace(old,new)
save(f.name,s+'\n#[path="r116_query.rs"]mod r116_query;\n')
save('r116_query_check.rs','''extern crate aspis_core as corelib;
use corelib::field::{QM31 as K,M31};
use corelib::sumcheck::WeightAccumulator;
#[derive(Debug,PartialEq)]enum Error{Shape}
mod r116_query;
fn main(){r116_query::controls();}
''')
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r116-query-check"\npath="../r116_query_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r116_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r115_native']['fixtures'],'changed':len(set(changed)),
 'query_fold_arithmetic_deferred':True,'transcript_messages_challenges_and_inc_unchanged':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed))}))
