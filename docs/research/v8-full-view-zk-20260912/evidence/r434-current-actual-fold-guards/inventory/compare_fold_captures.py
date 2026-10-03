#!/usr/bin/env python3
"""Strict Fun70 cross-capture comparison; only source spans and statement IDs are omitted."""
import argparse, hashlib, json
from pathlib import Path

ROOT=Path.cwd()
OLD=ROOT/'.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
NEW=ROOT/'.r21-scratch/r434-actual-fold-control/root-launch-a/saved-output/R434ActualFoldUbHelpers.llbc'
OUT=ROOT/'.r21-scratch/r434-actual-fold-control/inventory/fun70-cross-capture-comparison.json'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text())
def norm_fun(path):
    doc=load(path); tr=doc['translated']; defs={}
    def collect(x):
        if isinstance(x,dict):
            h=x.get('HashConsedValue')
            if isinstance(h,list) and len(h)==2:
                i,v=h
                if i in defs and defs[i]!=v: raise ValueError(f'hashcons collision {i}')
                defs[i]=v
            for y in x.values(): collect(y)
        elif isinstance(x,list):
            for y in x: collect(y)
    collect(tr)
    def expand(x,stack=()):
        if isinstance(x,dict):
            if set(x)=={'HashConsedValue'}:
                i,_=x['HashConsedValue']
                if i in stack: raise ValueError(f'hashcons cycle {stack+(i,)}')
                return expand(defs[i],stack+(i,))
            if set(x)=={'Deduplicated'}:
                i=x['Deduplicated']
                if i in stack: raise ValueError(f'dedup cycle {stack+(i,)}')
                return expand(defs[i],stack+(i,))
            is_stmt={'id','kind','span','comments_before'}<=set(x)
            return {k:expand(v,stack) for k,v in x.items()
                    if k not in ('span','generated_from_span') and not (is_stmt and k=='id')}
        if isinstance(x,list): return [expand(y,stack) for y in x]
        return x
    return doc,expand(tr['fun_decls'][70])

ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,default=OLD);ap.add_argument('--new',type=Path,default=NEW);ap.add_argument('--out',type=Path,default=OUT);a=ap.parse_args()
od,of=norm_fun(a.old); nd,nf=norm_fun(a.new)
diff=[]
def compare(x,y,path='$'):
    if type(x)!=type(y): diff.append({'path':path,'old_type':type(x).__name__,'new_type':type(y).__name__}); return
    if isinstance(x,dict):
        if set(x)!=set(y): diff.append({'path':path,'old_keys':sorted(x),'new_keys':sorted(y)}); return
        for k in x: compare(x[k],y[k],path+'/'+k)
    elif isinstance(x,list):
        if len(x)!=len(y): diff.append({'path':path,'old_length':len(x),'new_length':len(y)}); return
        for i,(u,v) in enumerate(zip(x,y)): compare(u,v,f'{path}/{i}')
    elif x!=y: diff.append({'path':path,'old':x,'new':y})
compare(of,nf)
result={'old_path':str(a.old.relative_to(ROOT)) if a.old.is_relative_to(ROOT) else str(a.old),'old_sha256':sha(a.old),
 'new_path':str(a.new.relative_to(ROOT)) if a.new.is_relative_to(ROOT) else str(a.new),'new_sha256':sha(a.new),
 'function_id':70,'comparison':'Fun70 rows expanded with each capture-local hash-cons/dedup table; only span, generated_from_span, and IDs on recognized statement records omitted.',
 'equal':not diff,'difference_count':len(diff),'differences':diff}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('old_sha256','new_sha256','equal','difference_count')}))
if diff: raise SystemExit(1)
