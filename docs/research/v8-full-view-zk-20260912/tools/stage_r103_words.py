#!/usr/bin/env python3
"""Isolate word-leaf encoding from the measured R102 authentication profile."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='87f8c0748b21cd11000f5352d29de588192942354b1e11def7801d7a399b2eee'
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
def replace(n,old,new):
    s=(ex/n).read_text();assert s.count(old)==1,(n,old[:90]);save(n,s.replace(old,new))
for n in ['r103_words.rs','r103_word_check.rs']:save(n,(here/n).read_text())
replace('relation_callback.rs','mod r102_tree;','mod r102_tree;\nmod r103_words;')
replace('relation_callback.rs','const REC:usize=621','const REC:usize=640')
replace('relation_callback.rs','b.len()>59138','b.len()>59556')
for n in ['relation_callback.rs','r17_host_relation.rs']:
    s=(ex/n).read_text()
    for old,new in [('r[589..621]','r[608..640]'),('r[..403]','r[..416]'),('r[403..589]','r[416..608]'),
       ('gamma_combine_v6_packed_layer0(','crate::r103_words::gamma_reference('),
       ('query_arithmetic::gamma(','crate::r103_words::gamma_reference('),
       ('query_arithmetic::combine_beta(','query_arithmetic::combine_words('),
       ('corelib::v6_onefold::packed_qm31_at(','crate::r103_words::qm31_at('),
       ('private_leaf_hash_v7(','crate::r103_words::leaf('),('leaf_record::c2(','crate::r103_words::c2(')]:s=s.replace(old,new)
    save(n,s)
# Keep every old packed decoder and differential; only add a new entry to the
# EXACT selected mixed-width arithmetic body with a different decoder boundary.
f=ex/'query_arithmetic.rs';s=f.read_text();start=s.index('#[inline(never)]\npub(super) fn combine_beta(');end=s.index('// Caller-owned decoded storage:',start)
body=s[start:end].replace('fn combine_beta(','fn combine_words(').replace('r55_decode_into(','crate::r103_words::decode(')
save('query_arithmetic.rs',s+'\n'+body)
profile='AV8/R103/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-word32-research-v1'
for n in ['performance_verifier.rs','payment_extraction.rs']:
    replace(n,m['r102_auth']['profile'],profile)
s=(ex/'performance.rs').read_text()
for old,new in [('c1leaf(&encoded,i)','crate::r103_words::c1leaf(&encoded,i)'),
    ('c2leaf(&c2encoded,i,false)','crate::r103_words::c2leaf(&c2encoded,i)'),
    ('private_leaf_hash_v7(','crate::r103_words::leaf('),('\\"max_body_bytes\\":59138','\\"max_body_bytes\\":59556')]:
    assert old in s,old;s=s.replace(old,new)
save('performance.rs',s)
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r103-word-check"\npath="../r103_word_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r103_words']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'profile':profile,'new_profile':True,'security_promoted':False,'source_coverage_proved':False,
 'c1_bytes':416,'c2_bytes':192,'record_bytes':640,'leaf_domain':32,'max_body_bytes':59556,
 'extra_record_bytes':418,'old_negative_sources_preserved':True,'requires_new_actual_affine_gates':True,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed)),'new_profile':True}))
