#!/usr/bin/env python3
"""Reconnect the existing proved shared-gamma kernel to current preparation."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='ddece23bc284c96ef9fc1d2e973701af7c2fdb347529941cd2bf7daf911c749a'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='95fbbdf3ed3acb9bd8fda2e8a130bad22e1ae14b58d9147f45044ef24ab3df94'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
kernel=ex/'shared_gamma.rs'
assert sha(kernel)=='75c26014c9900221445c14536d966f3d9267b53b331709099afda6374bf72552'
changed.append(kernel)
f=ex/'r17_host_relation.rs';s=f.read_text()
needle='    let gp = gamma.pow(27);\n    let batch = |v: &[K]| v.iter().rev().fold(K::ZERO, |a, v| a.mul(gamma).add(*v));'
assert s.count(needle)==1
s=s.replace(needle,'''    let gamma_powers=corelib::field::qm31_power_table::<29>(gamma);
    let gp=gamma_powers[27];
    let starts=[271usize,300,329,359,388];
    let rows=starts.map(|i|w.v[i..i+29].try_into().unwrap());
    let batches=shared_gamma::five(gamma_powers[1..].try_into().unwrap(),rows);
    #[cfg(not(target_os="solana"))]
    for i in 0..5 {
        let expected=rows[i].iter().rev().fold(K::ZERO,|a,v|a.mul(gamma).add(*v));
        assert_eq!(batches[i],expected,"R90 source public batch {i}");
    }''')
needle='scales[r].mul(batch(&w.v[271 + 29 * r..300 + 29 * r]))';assert s.count(needle)==1
s=s.replace(needle,'scales[r].mul(batches[r])')
needle='let all = [batch(&w.v[359..388]), batch(&w.v[388..417])];';assert s.count(needle)==1
s=s.replace(needle,'let all = [batches[3],batches[4]];')
s+='\n#[path="shared_gamma.rs"] mod shared_gamma;\n'
f.write_text(s);changed.append(f)
test=kernel.read_text().split('#[cfg(test)]\n',1)[1]
test=test.replace('    #[test]\n','').replace('fn independent_five_rows_match()','pub(super) fn run()')
test=test.replace('    use super::*;','    use super::*;\n    use shared_gamma::five;')
f=ex/'r90_gamma_check.rs'
f.write_text('''extern crate aspis_core as corelib;
use corelib::field::{QM31 as K,CM31,M31};
mod shared_gamma;
'''+test+'\nfn main(){tests::run();}\n');changed.append(f)
f=ex/'performance-host/Cargo.toml'
f.write_text(f.read_text()+'\n[[bin]]\nname="r90-gamma-check"\npath="../r90_gamma_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r90_gamma']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
    'reused_kernel_sha256':sha(kernel),'independent_outputs':5,
    'canonical_input_boundary':'Wire fields parsed canonically; gamma obtained from retained challenge sampler.',
    'transcript_and_errors_unchanged':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'reused_shared_gamma':True}))
