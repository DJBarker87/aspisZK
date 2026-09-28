#!/usr/bin/env python3
"""Host-only fixed-prefix capacity checker; no selected verifier changes."""
import argparse, hashlib, json, shutil, struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==182 and 'r27_shared_blocks'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists() and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
exrel=Path('docs/research/v8-no-work-100-20260907/experiments');ex=dst/exrel
source=(src/exrel/'r17_coupled_audit.rs').read_text()
def function(needle):
    start=source.index(needle);brace=source.index('{',start);depth=0
    for i in range(brace,len(source)):
        depth+=(source[i]=='{')-(source[i]=='}')
        if depth==0:return source[start:i+1]
    raise AssertionError(needle)
helpers='use super::*;\n'+'\n'.join(function(n) for n in ['pub(super) fn dot(', 'fn xt(', 'pub(super) fn chord(', 'pub(super) fn qvector(', 'pub(super) fn eval_weights('])+'\n'
(ex/'r28_source_helpers.rs').write_text(helpers)
shutil.copy2(here/'r28_h1_capacity.rs',ex/'r28_h1_capacity.rs')
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r28-h1-capacity"\npath="../r28_h1_capacity.rs"\n')
prefixes=[]
for world in range(2):
    log=src/f'r24-host-a/world{world}.log';lines=log.read_text().splitlines()
    captures=[json.loads(s.removeprefix('R19_PUBLIC_PREFIX '))for s in lines if s.startswith('R19_PUBLIC_PREFIX ')];assert len(captures)==1
    assert 'R17_PUBLIC_PREFIX_ACCEPTED'in lines
    capture=captures[0];assert len(capture['fields'])==336 and len(capture['queries'])==22
    b=bytes(capture['fields'])+b''.join(struct.pack('<I',q)for q in capture['queries'])
    prefix=dst/f'world{world}-prefix.bin';prefix.write_bytes(b)
    prefixes.append({'world':world,'capture_log':str(log),'capture_sha256':sha(log),'prefix_sha256':sha(prefix)})
for path in [ex/'r28_source_helpers.rs',ex/'r28_h1_capacity.rs',cargo]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r28_h1_capacity']={'control_manifest_sha256':sha(src/'r18-stage.json'),'helper_source_sha256':sha(src/exrel/'r17_coupled_audit.rs'),'prefixes':prefixes,'verifier_changed':False,'source_beta_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
