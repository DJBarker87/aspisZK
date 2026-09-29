#!/usr/bin/env python3
"""Exact-output shared pair and frozen descriptor, based on measured R86."""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='288fca8e72c88357ac54715268b7f36d020fbfe18d641a4a09fabf2adfb609f6'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='08a8b2d0a5627f3b31d84e07d214d90911366fbcbc42dbbfcc7449d7818e49d7'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def edit(n,fn):
    f=ex/n;s=f.read_text();new=fn(s);assert new!=s,n;f.write_text(new);changed.append(f)
edit('r17_compact_prepare.rs',lambda s:s+'\n'+(here/'r87_prepare_pair.rs').read_text())
table=(ex/'r17_basis_tables.rs').read_text()
order=ast.literal_eval(re.search(r'ORDER: \[usize; 1024\] = (\[[^;]+\]);',table)[1])
inactive=ast.literal_eval(re.search(r'INACTIVE: \[bool; 1024\] = (\[[^;]+\]);',table)[1].replace('true','True').replace('false','False'))
assert [order[j]for j in [0,1,2,1023]]==[14,15,30,1023]
assert all(inactive[r]for r in [14,15,30,1023])
prefix=b'AV8/R84/functional/sparseG-bitperm-two-swaps/channel-fold/v2'+b''.join(r.to_bytes(2,'little')for r in order)+bytes(inactive)
f=ex/'r87_descriptor.rs';f.write_text('// Generated from the source-export-checked fixed R84 map.\nconst R87_DESCRIPTOR_PREFIX:&[u8]=&'+str(list(prefix))+';\n');changed.append(f)
def prepare(s):
    old='let shared_pair=if !dense_ordinary {crate::r17_compact_prepare::ordinary_pair(&s.z,kappa,use_x)} else {[K::ZERO;2]};'
    new='let (shared_pair,first_pair)=if !dense_ordinary {crate::r17_compact_prepare::ordinary_and_first(&s.z,kappa,use_x)} else {([K::ZERO;2],[K::ZERO;2])};'
    assert s.count(old)==1;s=s.replace(old,new)
    old='let e=crate::r18_compact_g::first_pair(&s.z,use_x);';assert s.count(old)==1;s=s.replace(old,'let e=first_pair;')
    start=s.index('    let mut descriptor = b"AV8/R84/functional/')
    end=s.index('    // Fixed framing:',start);old=s[start:end]
    s=s[:start]+'''    let mut descriptor=R87_DESCRIPTOR_PREFIX.to_vec();
    #[cfg(not(target_os="solana"))] {
'''+old+'''        assert_eq!(descriptor,R87_DESCRIPTOR_PREFIX);
    }
'''+s[end:]
    return s+'\ninclude!("r87_descriptor.rs");\n'
edit('r17_host_relation.rs',prepare)
def check(s):
    s=s.replace('mod r17_tensor_prefix;','mod r17_tensor_prefix;\nmod r17_compact_prepare;\nmod r18_compact_g;\nmod r20_sparse_whole;\nmod r20_private_dot_adapter;')
    needle='        let k=sample(&mut seed);let k2=k.square();let scales=[k,k2,k2.mul(k)];'
    assert s.count(needle)==1
    return s.replace(needle,needle+'\n        for use_x in [false,true] {r17_compact_prepare::r87_check(&source_z,k,use_x);}')
edit('r84_bitperm_check.rs',check)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r87_prepare']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
    'descriptor_prefix_bytes':len(prefix),'descriptor_prefix_sha256':hashlib.sha256(prefix).hexdigest()}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'descriptor_prefix_bytes':len(prefix)}))
