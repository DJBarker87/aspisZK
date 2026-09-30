#!/usr/bin/env python3
"""Isolate the same-profile, same-hash-order one-buffer Merkle walk."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='94133394e2f68a0f1b59e6b2853945ce2b9356dfc03c343dc50074276d80a20f'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='0e175a42b6c91873ab85af136802bb58f5b1fa51ca7d48940f74ef792fa7e00d'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
for n in ['r95_merkle.rs','r95_merkle_check.rs']:
    f=ex/n;shutil.copy2(here/n,f);changed.append(f)
f=ex/'relation_callback.rs';s=f.read_text();needle='mod r17_host_relation;';assert s.count(needle)==1
f.write_text(s.replace(needle,'mod r95_merkle;\n'+needle));changed.append(f)
f=ex/'r17_host_relation.rs';s=f.read_text();start=s.index('pub(super) fn opened_channel(')
needle='''if !verify_two_minimal_subtrees_v7_bytes(
        hash,
        (&w.roots.0, &w.roots.1),
        18,
        &entries,
        w.frontiers,
        &mut vec![],
        &mut vec![],
    )'''
assert s[start:].count(needle)==1
s=s[:start]+s[start:].replace(needle,'''if !crate::r95_merkle::verify(hash,(&w.roots.0,&w.roots.1),18,&entries,w.frontiers)''',1)
f.write_text(s);changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r95-merkle-check"\npath="../r95_merkle_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r95_merkle']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'hash_call_order_changed':False,'new_security_claim':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
