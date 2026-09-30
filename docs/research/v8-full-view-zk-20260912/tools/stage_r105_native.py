#!/usr/bin/env python3
"""Independent same-proof fixed parser and Copy-registry candidates."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--variant',choices=['parse','gather'],required=True);p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
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
def save(f,s):f.write_text(s);changed.append(f)
if a.variant=='parse':
    save(ex/'r105_parse.rs',(here/'r105_parse.rs').read_text())
    f=ex/'relation_callback.rs';s=f.read_text();s=s.replace('mod r102_tree;','mod r102_tree;\nmod r105_parse;')
    old='b[..FIXED*16].chunks_exact(16).map(|x|K::from_le_bytes(x).ok_or(Error::Canonical)).collect::<Result<Vec<_>,_>>()?'
    assert s.count(old)==1;save(f,s.replace(old,'r105_parse::fields(&b[..FIXED*16])?'))
    save(ex/'r105_parse_check.rs','extern crate aspis_core as corelib;\nuse corelib::field::{M31,CM31,QM31 as K};\n#[derive(Debug,PartialEq)]enum Error{Length,Canonical}\nmod r105_parse;\nfn main(){r105_parse::controls();}\n')
    f=ex/'performance-host/Cargo.toml';save(f,f.read_text()+'\n[[bin]]\nname="r105-parse-check"\npath="../r105_parse_check.rs"\n')
else:
    folder=dst/'crates/aspis-statement/src/pool_v1';f=folder/'r57_selector_gather.rs';s=f.read_text()
    assert s.count('fn r57_gather(')==1
    save(f,s.replace('fn r57_gather(','fn r105_retained_gather(')+'\ninclude!("r105_gather.rs");\n')
    save(folder/'r105_gather.rs',(here/'r105_gather.rs').read_text())
    f=ex/'r57_selector_check.rs';s=f.read_text();assert s.count('fn main(){')==1
    save(f,s.replace('fn main(){','fn main(){println!("R105_COALESCED old_terms=544 new_terms={} exact_integer_map=true",aspis_statement::pool_v1::pair_forest_copy_terminal::r105_table_controls());'))
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r105_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),'variant':a.variant,
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':[{'path':str(src/f'r24-host-a/fixture-world{w}'),'sha256':sha(src/f'r24-host-a/fixture-world{w}/proof-1.bin')}for w in range(2)],'changed':len(set(changed))}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed)),'variant':a.variant}))
