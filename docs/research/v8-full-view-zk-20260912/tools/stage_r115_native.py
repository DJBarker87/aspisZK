#!/usr/bin/env python3
"""Compose measured exact-output winners, rejecting unexpected source conflicts."""
import argparse, hashlib, json, shutil
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--include-tag',action='store_true')
a=p.parse_args(); src=a.control; dst=a.output
def sha(f): return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f): return json.loads(f.read_text())
assert sha(src/'r18-stage.json')=='1455a58e904b3b803c46de43686c73733b5c58a69f1bf391cc5d5190fbb1a296'
m=read(src/'r18-stage.json')
for n,h in m['files'].items(): assert sha(src/n)==h,n
variants=[
 ('r106','aspis-r20-r106-terminal-20260930-a','2d2fc00941ccacd99e9ec12738259194d32fc84d34246cccca24a543200886fb'),
 ('r107','aspis-r20-r107-semantic-20260930-a','da2cbde5b93005e4889288f9bbcdf3cd7c9da7ae813fe96b2daeba8e2fc4ac19'),
 ('r109','aspis-r20-r109-geometry-20260930-a','335f0689a34fc8a5664cd4cf0c01c4ab96fcf15a3b146057584cf8b6360be892'),
 ('r112','aspis-r20-r112-complex-20260930-a','9c14128ccaf88a7b2fa80942e94947ba3af8d4e20f150e1f2f184a6b3551c42e'),
 ('r113','aspis-r20-r113-copy-20260930-b','00288a778e184ced8ec0b35ac0471b8cff12aed501e5c3cc80eb1b409f8a40aa')]
if a.include_tag:
    variants.append(('r114','aspis-r20-r114-tag-20260930-a','dc7a56b97adf9e883463ff945ffdc7ee3da199ae8ddaa92b5578fcf8f3e64521'))
cargo='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
original_cargo=(src/cargo).read_text(); suffixes=[]; chosen={}; records=[]
fixtures=m['r105_native']['fixtures']
for key,folder,pin in variants:
    stage=src.parent/folder; cm=read(stage/'r18-stage.json')
    assert sha(stage/'r18-stage.json')==pin
    receipt=read(stage/'r24-svm-a/receipt.json')
    assert receipt['source_manifest_sha256']==pin and receipt['full_verifier'] and not receipt['new_profile']
    assert not receipt['security_promoted']
    assert [x['proof_sha256']for x in receipt['runs']]==[x['sha256']for x in fixtures]
    measured=[]
    for run in receipt['runs']:
        high=next(x for x in run['results']if x['case']=='honest'and x['cu_limit']==100000000)
        assert high['accepted']and not high['resource_failure']
        measured.append(high['cu'])
        assert all(x['heap_bytes']==262144 and x['unchanged_accounts']for x in run['results'])
        assert all(x['custom_rejection']and not x['resource_failure']for x in run['results']if x['case']=='bad-combined-final')
    assert all(x<y for x,y in zip(measured,[1066127,1065886])),(key,measured)
    delta={}
    for n,h in cm['files'].items():
        assert sha(stage/n)==h,n
        if m['files'].get(n)==h: continue
        delta[n]=h
        if n==cargo:
            text=(stage/n).read_text(); assert text.startswith(original_cargo)
            suffixes.append(text[len(original_cargo):]); continue
        if n in chosen: assert chosen[n][1]==h,('conflicting sources',n)
        chosen[n]=(stage/n,h)
    records.append({'key':key,'stage':str(stage),'manifest_sha256':pin,
                    'receipt_sha256':sha(stage/'r24-svm-a/receipt.json'),'isolated_cu':measured,'delta':delta})
assert not dst.exists(); dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
for n,(path,h)in chosen.items():
    (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,dst/n);assert sha(dst/n)==h
    m['files'][n]=h
# R112's host-only differential module uses the corelib alias. The standalone
# R107 host harness did not previously import it; production source is unchanged.
harness='docs/research/v8-no-work-100-20260907/experiments/r107_semantic_check.rs'
(dst/harness).write_text('extern crate aspis_core as corelib;\n'+(dst/harness).read_text())
m['files'][harness]=sha(dst/harness)
# Candidate Cargo changes are append-only bin declarations, never dependencies.
assert all(s.strip().startswith('[[bin]]')for s in suffixes)
(dst/cargo).write_text(original_cargo+''.join(suffixes)); m['files'][cargo]=sha(dst/cargo)
m['r115_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':fixtures,'changed':len(chosen)+1,'candidates':records,'include_tag':a.include_tag,
 'composition_CU_measured':False,'isolated_savings_not_added':True,
 'host_harness_alias_repair':harness,'prior_failure':'r115-composed-a: missing corelib alias in host-only R107 harness; exit 101'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(chosen)+1,'variants':[x[0]for x in variants]}))
