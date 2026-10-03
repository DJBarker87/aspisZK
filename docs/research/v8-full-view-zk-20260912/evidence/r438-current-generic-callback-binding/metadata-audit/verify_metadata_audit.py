#!/usr/bin/env python3
"""Independent R438 metadata audit; reads the finalized inventory only."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path

DEFAULT = Path(__file__).resolve().parents[1] / 'inventory'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def canon(x): return json.dumps(x, sort_keys=True, separators=(',', ':'))
def walk(x, path='$'):
    if isinstance(x, dict):
        yield path, x
        for k,v in x.items(): yield from walk(v, f'{path}.{k}')
    elif isinstance(x, list):
        for i,v in enumerate(x): yield from walk(v, f'{path}[{i}]')

def run(inv, out):
    inv=Path(inv); out=Path(out)
    src=inv/'R437PointerWrapperLayout.llbc'
    raw=json.loads(src.read_text()); assert raw['has_errors'] is False
    t=raw['translated']; funs=t['fun_decls']
    slots=json.loads((inv/'function-source-slots.json').read_text())
    desc=json.loads((inv/'function-source-descriptors.json').read_text())
    sel=json.loads((inv/'selector-inventory.json').read_text())
    assert len(funs)==159 and len(slots)==159
    populated=[]; derived=[]; absent=[]
    for i,f in enumerate(funs):
        if f is None:
            absent.append(i)
            derived.append({'absent_slot':True,'fun_id':None,'name':None,'slot_index':i,'src':None})
            continue
        assert f['def_id']==i, (i,f['def_id'])
        s={'fun_id':i,'slot_index':i,'name':f['item_meta']['name'],'span':f['item_meta']['span'],'src':f['src']}
        populated.append(s); derived.append({'absent_slot':False,**s})
    # The full slot records and descriptor rows must exactly match raw decoded JSON fields.
    assert canon(slots)==canon(derived)
    assert canon(desc)==canon(populated)
    counts=Counter()
    for x in populated:
        kind=x['src'] if isinstance(x['src'],str) else next(iter(x['src']))
        counts[kind]+=1
    assert counts==Counter({'TopLevel':91,'TraitImpl':60,'TraitDecl':5}), counts
    assert absent==[6,127,131]
    # Recompute selector from every populated source descriptor, not from its saved match list.
    candidates=[]
    for x in populated:
        srcx=x['src'].get('TraitImpl') if isinstance(x['src'],dict) else None
        if srcx and srcx['impl_ref']['id']==35 and srcx['item_id']=={'Method':0}:
            candidates.append(x)
    assert len(candidates)==1 and candidates[0]['fun_id']==112
    f112=funs[112]; s112=f112['src']['TraitImpl']
    assert s112['reuses_default'] is False and s112['trait_ref']['id']==3
    assert candidates[0]['name'][-1]=={'Ident':['call_mut',0]}
    # Independently locate the fold call in function 70 by recursively scanning native JSON.
    hits=[]
    for path,node in walk(funs[70]['body']):
        if not isinstance(node,dict) or 'Call' not in node.get('kind',{}): continue
        call=node['kind']['Call']['call']; fn=call.get('func',{}).get('Regular',{}).get('kind',{}).get('Trait')
        if fn and fn[0].get('HashConsedValue',[None,{}])[1].get('kind',{}).get('TraitImpl',{}).get('id')==35:
            hits.append((path,call))
    assert len(hits)==1
    call_path, call=hits[0]
    assert call['func']['Regular']['kind']['Trait'][0]['HashConsedValue'][1]['kind']['TraitImpl']['id']==35
    td=t['trait_decls'][3]; ti=t['trait_impls'][35]
    assert td['item_meta']['name'][-1]=={'Ident':['FnMut',0]}
    assert td['methods']==[] and ti['methods']==[]
    assert sel['selector']['matched_count']==1 and sel['selector']['matched_fun_ids']==[112]
    assert sel['callsite']['match_count']==1
    # Validate pinned Charon source copies against their full-file SHA pins.
    pin=json.loads((inv/'pinned-charon/source-pins.json').read_text())
    src_checks=[]
    for row in pin['source_files']:
        p=inv/row['copy']; got=sha(p); assert got==row['sha256'], row['copy']
        src_checks.append({'copy':row['copy'],'sha256':got,'source_path':row['path'],'lines':row['lines']})
    astpin=json.loads((inv/'pinned-charon/generated-ast-source-pins.json').read_text())
    ast_checks=[{'source_path':row['path'],'source_sha256':row['sha256'],'lines':row['lines'],'excerpt_file':row['excerpt']} for row in astpin['sources']]
    # The native generated-AST source files are not copied here; only their pinned
    # remote hashes and selected line excerpts are retained. Verify excerpt custody.
    assert (inv/'pinned-charon/source-excerpts.txt').is_file()
    assert pin['charon_source_commit']==astpin['charon_source_commit']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c'
    # Hash inventory itself, excluding only its root SHA256SUMS index.
    listed={}
    for line in (inv/'SHA256SUMS').read_text().splitlines():
        h, rel=line.split('  ',1); listed[rel]=h
    actual={p.relative_to(inv).as_posix():sha(p) for p in inv.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
    assert listed==actual, ('inventory checksum set mismatch',len(listed),len(actual))
    out.mkdir(parents=True,exist_ok=True)
    report={
      'status':'PASS', 'inventory_path':str(inv), 'input_llbc_sha256':sha(src),
      'has_errors':raw['has_errors'], 'function_slots':len(funs),
      'populated_descriptors':len(populated), 'absent_slots':absent,
      'source_variant_counts':dict(counts), 'selected_function':112,
      'selected_source_kind':'TraitImpl', 'selected_impl_id':35,
      'selected_trait_id':3, 'selected_item_id':{'Method':0},
      'selected_reuses_default':False, 'selected_source_span':f112['item_meta']['span'],
      'selected_name':f112['item_meta']['name'], 'fold_function_id':70,
      'fold_call_count':len(hits), 'fold_call_json_path':call_path,
      'trait_decl_3_name':td['item_meta']['name'], 'trait_decl_3_methods':td['methods'],
      'trait_impl_35_methods':ti['methods'], 'source_pins':src_checks,
      'generated_ast_source_pins':ast_checks,
      'pinned_charon_commit':pin['charon_source_commit'],
      'boundary':'Metadata audit only: confirms captured LLBC source descriptors and pinned translation-source facts. Does not establish trait dispatch execution, source/model equivalence, or semantic adequacy.'
    }
    (out/'audit-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    return report
if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--inventory',default=str(DEFAULT)); ap.add_argument('--out',default=str(Path(__file__).resolve().parent)); a=ap.parse_args()
    r=run(a.inventory,a.out); print(json.dumps({k:r[k] for k in ['status','function_slots','populated_descriptors','source_variant_counts','selected_function','fold_call_json_path']}))
