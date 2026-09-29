#!/usr/bin/env python3
"""Collect field-lift/degree proofs and the unchanged source challenge boundary."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output;assert not out.exists();out.mkdir();parent=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
copy(a.stage/'r18-stage.json','r18-stage.json')
ex='docs/research/v8-no-work-100-20260907/experiments/'
selected=[ex+n for n in['r17_host_relation.rs','relation_callback.rs','inactive_row_binding.rs']]+['crates/aspis-core/src/'+n for n in['transcript.rs','circle.rs','circle_fri.rs']]
for n in selected:assert n in m['files'];copy(a.stage/n,'source/'+n)
for letter in 'abcdef':
    for f in(parent/f'aspis-r41-lean-20260929-{letter}').glob('*'):
        if f.suffix in['.json','.log']:copy(f,'lean-'+letter+'/'+f.name)
(out/'receipt.json').write_text(json.dumps({'parent_revision':'9a9b2142709edc9a7066eab68acb09cbe4690731','source_manifest_sha256':sha(a.stage/'r18-stage.json'),'source_pins':len(m['files']),'inspected_source_files':selected,'new_lean_declarations':34,'reused_tower_leaf_compiled':True,'coefficient_field':'AspisV8R15.ExactTowerBase.QM31Exact','total_degree_bound':1105,'query_count':22,'query_domain_size':262144,'query_draw_cap':64,'lean_scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'source_runtime_rerun':False,'source_distribution_bound':False,'full_privacy':False,'verifier_changed':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n');print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
