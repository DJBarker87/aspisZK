#!/usr/bin/env python3
import json, hashlib
from pathlib import Path
base=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
out=base/'.r21-scratch/r434-actual-fold-control/closure-inventory'
llbc=base/'.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
rust=base/'.r21-scratch/r429-actual-freeze-fold/materialized-release-check/input/relation_callback.rs'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
doc=json.loads(llbc.read_text()); x=doc['translated']
ids=[29,70,111,112,144]
rows={'fun_decls':{str(i):x['fun_decls'][i] for i in ids},'type_decls':{'50':x['type_decls'][50]},'trait_impls':{'35':x['trait_impls'][35]}}
(out/'R431-exact-rows.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
# Source excerpt: exact requested freeze ranges and declarations around them.
lines=rust.read_text().splitlines(keepends=True)
(out/'frozen-source-excerpt.txt').write_text(''.join(f'{i+1:4d} {lines[i]}' for i in range(125,140)))
# Enumerate statement-level Call/Drop sites plus unwind ladders for selected bodies.
sites=[]
def walk(obj,path,fun):
    if isinstance(obj,dict):
        for k,v in obj.items():
            p=path+'/'+k
            if k in ('Call','Drop'):
                sites.append({'fun_id':fun,'path':p,'kind':k,'node':v})
            walk(v,p,fun)
    elif isinstance(obj,list):
        for i,v in enumerate(obj): walk(v,path+f'/{i}',fun)
for i in ids:
    b=x['fun_decls'][i]['body']
    walk(b,f'fun_decls/{i}/body',i)
(out/'call-drop-unwind-sites.json').write_text(json.dumps(sites,indent=2,ensure_ascii=False)+'\n')
meta={
 'frozen_source':{'path':str(rust.relative_to(base)),'sha256':sha(rust)},
 'r431_llbc':{'path':str(llbc.relative_to(base)),'sha256':sha(llbc)},
 'selected_rows':{'fun_decls':ids,'type_decls':[50],'trait_impls':[35]},
 'source_ranges':[
  {'rust_lines':'129','text':'record.extend(bytes(&w.v[359..388]))','role':'first batch slice bytes included in transcript record'},
  {'rust_lines':'131','text':'record.extend(bytes(&w.v[388..417]))','role':'second batch slice bytes included in transcript record'},
  {'rust_lines':'134','text':lines[133].strip(),'role':'batch closure and fold body'},
  {'rust_lines':'136-137','text':'lines included in frozen-source-excerpt.txt','role':'batch calls for both slices and inverse construction'}],
 'fact_boundary':'This inventory reports exact frozen source text and captured R431 LLBC rows/sites only. It does not assert Rust-to-LLBC execution correspondence, aliasing, lifetimes, or frame premises.'}
(out/'inventory.json').write_text(json.dumps(meta,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'source_sha256':meta['frozen_source']['sha256'],'llbc_sha256':meta['r431_llbc']['sha256'],'rows_bytes':(out/'R431-exact-rows.json').stat().st_size,'site_count':len(sites),'site_file_bytes':(out/'call-drop-unwind-sites.json').stat().st_size},indent=2))
