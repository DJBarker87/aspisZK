#!/usr/bin/env python3
"""Collect residual specialization/nonzero evidence, including failed plumbing."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output;assert not out.exists();out.mkdir();parent=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
copy(a.stage/'r18-stage.json','r18-stage.json');copy(a.stage/'r17-stage.json','r17-stage.json');ex='docs/research/v8-no-work-100-20260907/experiments/'
for n in['r40_entry_generator.rs','performance-host/Cargo.toml']:copy(a.stage/(ex+n),'source/'+ex+n)
for f in(a.stage/'check-a').glob('*'):
    if f.is_file()and f.suffix in['.json','.log']:copy(f,'runtime/'+f.name)
prior=parent/'aspis-r37-source-20260929-b/check-a/results/algebraic-witness-minor.bin';copy(prior,'runtime/retained-r37-minor.bin')
for letter in 'ab':
    old=parent/f'aspis-r40-generator-20260929-{letter}'
    for n in['compile.log','write.log','check.log','metadata.json','generated/WitnessQuotient00.lean','generated/WitnessEntryColumn00.lean']:copy(old/'check-a'/n,f'attempt-{letter}/'+n)
    copy(old/(ex+'r40_entry_generator.rs'),f'attempt-{letter}/r40_entry_generator.rs')
old=parent/'aspis-r40-generator-20260929-c';copy(old/'check-a/generated/WitnessNonzero.lean','attempt-c/WitnessNonzero.lean')
copy(old/(ex+'r40_entry_generator.rs'),'attempt-c/r40_entry_generator.rs')
for letter in 'abcdefn':
    for f in(parent/f'aspis-r40-lean-20260929-{letter}').glob('*'):
        if f.suffix in['.json','.log']:copy(f,'lean-'+letter+'/'+f.name)
(out/'receipt.json').write_text(json.dumps({'parent_revision':'84059b5296757f31bfc40f0be52e31de76aa2894','stage':str(a.stage),'source_manifest_sha256':sha(a.stage/'r18-stage.json'),'source_pins':len(m['files']),'generated_files':44,'new_lean_declarations':481,'quotient_coordinate_checks':1404,'combined_weight_checks':216,'model_minor_entries':169,'inverse_product_entries':169,'retained_r37_minor_sha256':sha(prior),'rust_scope':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'lean_scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'coefficient_ring':'ZMod 2147483647','nonzero_kernel_certificate':True,'source_distribution_bound':False,'full_privacy':False,'verifier_changed':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n');print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
