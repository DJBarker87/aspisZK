#!/usr/bin/env python3
"""Stage an AUTHENTICATION-ONLY pilot, not an alternative accepting verifier."""
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
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
changed=[]
for n in ['r101_merkle.rs','r101_auth_micro.rs','r101_auth_check.rs']:
    f=ex/n;shutil.copy2(here/n,f);changed.append(f)
f=ex/'performance-sbf/Cargo.toml';s=f.read_text();assert s.count('path = "../relation_callback.rs"')==1
f.write_text(s.replace('path = "../relation_callback.rs"','path = "../r101_auth_micro.rs"'));changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r101-auth-check"\npath="../r101_auth_check.rs"\n');changed.append(f)
driver=dst/'svm-driver';(driver/'src').mkdir(parents=True)
old=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a')
original=old/'src/main.rs';s=original.read_text()
assert s.count('proof[697 * 16] ^= 1;')==1 and s.count('assert!(original.len() > 699 * 16);')==1
s=s.replace('proof[697 * 16] ^= 1;','proof[20] ^= 1;').replace('assert!(original.len() > 699 * 16);','assert!(original.len() >= 72);')
s=s.replace('bad-combined-final','bad-auth-root').replace('R20 candidate verifier only; no settlement; security unproved',
    'R101 authentication-only benchmark; synthetic public leaves; NOT proof verification')
(driver/'src/main.rs').write_text(s);changed.append(driver/'src/main.rs')
for n in ['Cargo.toml','Cargo.lock']:shutil.copy2(old/n,driver/n);changed.append(driver/n)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
(dst/'r101-stage.json').write_text(json.dumps({'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'files':m['files'],'full_verifier':False,'actual_proof_fixtures':False,'security_promoted':False,
 'driver_original_source_sha256':sha(original),'new_encoding_installed':False,
 'scope':'Isolated paired authentication including header/entry/frontier parsing. Public synthetic full trees, same 22 indices across arities.'},indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'full_verifier':False}))
