#!/usr/bin/env python3
"""Isolated R27-output-preserving decoder experiments; exact parent pins."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);p.add_argument('--branchless',action='store_true');a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def function(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
assert sha(src/'r18-stage.json')=='3c0741beddf4bc794a0e21fccc38fcfda7fd9aa227b0b2a3104d8121bd147f79'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==182 and 'r27_shared_blocks'in m
for name,h in m['files'].items():assert sha(src/name)==h,name
assert not dst.exists()and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
path=ex/'query_arithmetic.rs';s=path.read_text();old=function(s,'pub(super) fn combine_beta(')
start=old.index('    #[cfg(v8_decode_profile)]');end=old.index('    let mut out=')
new=old[:start]+'''    let mut c1_values=[0u32;104];
    r55_decode_into(c1,&mut c1_values)?;
    let mut c2_values=[0u32;48];
    r55_decode_into(c2,&mut c2_values)?;
    let c1=&c1_values;let c2=&c2_values;
'''+old[end:]
s=s.replace(old,new)
helper=(here/'r55_decode_into.rs').read_text()
if a.branchless:
    helper=helper.replace('invalid|=u32::from(value==corelib::field::P);',
        '// value<=P, so value+1<=2^31: bit 31 marks exactly P.\n            invalid|=value+1;')
    helper=helper.replace('if invalid!=0','if invalid>>31!=0')
s+='\n'+helper+'\n#[cfg(not(v8_performance_sbf))]\n'+old.replace('fn combine_beta(','fn r55_reference_combine_beta(')+'\n'+(here/'r55_opening_controls.rs').read_text()
path.write_text(s)
checker=ex/'r55_opening_check.rs'
checker.write_text('''extern crate aspis_core as corelib;
use corelib::{field::{M31,CM31,QM31 as K},state_only_spend_query::StateOnlySpendQueryPowers,
    v6_onefold::gamma_combine_v6_packed_layer0};
#[derive(Debug,PartialEq)]enum Error{Length,Canonical}
mod query_arithmetic;
fn main(){query_arithmetic::r55_controls();}
''')
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r55-opening-check"\npath="../r55_opening_check.rs"\n')
for f in [path,checker,cargo]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r55_opening']={'base_revision':'85f18af7ce9078b751ca1b8fb981f1ce35396499',
    'control_manifest_sha256':sha(src/'r18-stage.json'),'branchless_canonicality':a.branchless,
    'caller_owned_decode':True,'protocol_changed':False,'validation_removed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'branchless':a.branchless}))
