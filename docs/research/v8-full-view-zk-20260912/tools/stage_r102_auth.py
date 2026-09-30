#!/usr/bin/env python3
"""Versioned full-source 8-way Merkle experiment. The R99 control is untouched."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='349f0dcadb4a1c3f61f33c692fb67c34cec3813883403b5fbdfb90cca77d0050'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def edit(name,old,new):
    f=ex/name;s=f.read_text();assert s.count(old)==1,(name,old[:90]);f.write_text(s.replace(old,new));changed.append(f)
for n in ['r101_merkle.rs','r102_tree.rs','r102_auth_check.rs']:
    f=ex/n;shutil.copy2(here/n,f);changed.append(f)
edit('relation_callback.rs','mod r95_merkle;','mod r95_merkle;\nmod r101_merkle;\nmod r102_tree;')
edit('relation_callback.rs','b.len()>40314','b.len()>59138')
# Keep both independently implemented opening arithmetic paths. Only their
# authentication adapter changes to the independently rebuilt 8-way reference.
f=ex/'relation_callback.rs';s=f.read_text();old='verify_two_minimal_subtrees_v7_bytes(hashfn,(&w.roots.0,&w.roots.1),18,&entries,w.frontiers,&mut vec![],&mut vec![])'
assert s.count(old)==2;s=s.replace(old,'crate::r102_tree::verify_reference(hashfn,(&w.roots.0,&w.roots.1),6,&entries,w.frontiers)');f.write_text(s);changed.append(f)
edit('r17_host_relation.rs','''verify_two_minimal_subtrees_v7_bytes(
        hash,
        (&w.roots.0, &w.roots.1),
        18,
        &entries,
        w.frontiers,
        &mut vec![],
        &mut vec![],
    )''','''crate::r102_tree::verify_reference(hash,(&w.roots.0,&w.roots.1),6,&entries,w.frontiers)''')
edit('r17_host_relation.rs','crate::r95_merkle::verify(hash,(&w.roots.0,&w.roots.1),18,&entries,w.frontiers)',
 'crate::r101_merkle::verify::<8>(hash,(&w.roots.0,&w.roots.1),6,&entries,w.frontiers)')
profile='AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1'
for n in ['performance_verifier.rs','payment_extraction.rs']:
    edit(n,'AV8/R84/sparseG-bitperm-two-swaps/quadratic-channel-fold/research-v2',profile)
for tree in ['a','b']:
    edit('performance.rs',f'let {tree}=tree(',f'let {tree}=crate::r102_tree::tree(hash,')
    edit('performance.rs',f'f::frontier(&{tree},&queries)',f'crate::r102_tree::frontier(&{tree},&queries)')
edit('performance.rs','\\"max_body_bytes\\":44378','\\"max_body_bytes\\":59138')
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r102-auth-check"\npath="../r102_auth_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r102_auth']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'profile':profile,'new_profile':True,'security_promoted':False,'source_coverage_proved':False,
 'mask_map_changed':False,'queries':22,'digest_bytes':26,'arity':8,'depth':6,
 'max_frontier_nodes':658,'max_body_bytes':59138,'old_negative_sources_preserved':True,
 'requires_new_actual_affine_gates':True,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed)),'new_profile':True}))
