#!/usr/bin/env python3
"""Strict structural comparison of the requested R429/R431 constant graph rows."""
import hashlib,json
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r433-actual-constructor-fragment/inventory'
OLD=ROOT/'.r21-scratch/r429-actual-freeze-fold/root-launch-c/saved-output/R429ActualFreezeFold.llbc'
NEW=ROOT/'.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
FUN_MAP={142:143,145:146,153:154}
OLD_FUNS=[142,145,153]; NEW_FUNS=[143,146,154]
GLOBALS=[31,32]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def collect_hashcons(translated):
    defs={}; conflicts=[]
    def walk(x):
        if isinstance(x,dict):
            h=x.get('HashConsedValue')
            if isinstance(h,list) and len(h)==2:
                i,v=h
                if i in defs and defs[i]!=v:conflicts.append(i)
                defs[i]=v
            for v in x.values():walk(v)
        elif isinstance(x,list):
            for v in x:walk(v)
    walk(translated)
    if conflicts:raise ValueError(f'conflicting hashcons entries: {sorted(set(conflicts))}')
    return defs

def normalize(x,defs,path='$',stack=()):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}:
            pair=x['HashConsedValue']
            if not isinstance(pair,list) or len(pair)!=2:raise ValueError(f'malformed HashConsedValue at {path}')
            i,value=pair
            if i in stack:raise ValueError(f'cyclic hashcons at {path}: {stack+(i,)}')
            return normalize(value,defs,path+'/HashConsedValue',stack+(i,))
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated']
            if i not in defs:raise ValueError(f'unresolved Deduplicated {i} at {path}')
            if i in stack:raise ValueError(f'cyclic Deduplicated {i} at {path}: {stack+(i,)}')
            return normalize(defs[i],defs,path+f'/Deduplicated({i})',stack+(i,))
        # These are the only omitted metadata fields.
        result={}
        is_stmt=('kind' in x and 'comments_before' in x and 'id' in x and 'span' in x)
        for k,v in x.items():
            if k in ('span','generated_from_span'):continue
            if k=='id' and is_stmt:continue
            if k=='def_id' and isinstance(v,int):v=FUN_MAP.get(v,v)
            if k=='Regular' and path.endswith('/kind/Fun') and isinstance(v,int):v=FUN_MAP.get(v,v)
            result[k]=normalize(v,defs,path+'/'+str(k),stack)
        return result
    if isinstance(x,list):return [normalize(v,defs,path+f'/{i}',stack) for i,v in enumerate(x)]
    return x

def diff(a,b,path='$',out=None):
    if out is None:out=[]
    if type(a)!=type(b):out.append({'path':path,'left':type(a).__name__,'right':type(b).__name__});return out
    if isinstance(a,dict):
        if a.keys()!=b.keys():out.append({'path':path,'left_keys':sorted(a.keys()),'right_keys':sorted(b.keys())})
        for k in sorted(a.keys()&b.keys()):diff(a[k],b[k],path+'/'+str(k),out)
    elif isinstance(a,list):
        if len(a)!=len(b):out.append({'path':path,'left_length':len(a),'right_length':len(b)})
        for i,(u,v) in enumerate(zip(a,b)):diff(u,v,path+f'/{i}',out)
    elif a!=b:out.append({'path':path,'left':a,'right':b})
    return out
old=load(OLD);new=load(NEW); od=old['translated'];nd=new['translated']
assert old.get('has_errors') is False and new.get('has_errors') is False
olddefs=collect_hashcons(od);newdefs=collect_hashcons(nd)
old_rows={'functions':{str(i):od['fun_decls'][i] for i in OLD_FUNS},'globals':{str(i):od['global_decls'][i] for i in GLOBALS}}
new_rows={'functions':{str(i):nd['fun_decls'][i] for i in NEW_FUNS},'globals':{str(i):nd['global_decls'][i] for i in GLOBALS}}
# Rename top-level function row keys and all function references according to the exact listed map.
new_renamed={'functions':{str(oldid):new_rows['functions'][str(newid)] for oldid,newid in zip(OLD_FUNS,NEW_FUNS)},'globals':new_rows['globals']}
# Normalize rows with per-capture hash-cons tables. Def ids and Fun.Regular references are mapped by normalize.
a=normalize(old_rows,olddefs);b=normalize(new_renamed,newdefs)
differences=diff(a,b)
report={
 'old_input':{'path':str(OLD.relative_to(ROOT)),'sha256':sha(OLD),'size_bytes':OLD.stat().st_size},
 'new_input':{'path':str(NEW.relative_to(ROOT)),'sha256':sha(NEW),'size_bytes':NEW.stat().st_size},
 'row_mapping':{'functions':{str(i):j for i,j in FUN_MAP.items()},'globals':{str(i):i for i in GLOBALS}},
 'hashcons_resolution':{'old_unique_definitions':len(olddefs),'new_unique_definitions':len(newdefs),'conflicts':0,'deduplicated_ids_resolved_recursively':True},
 'normalization_ignored_fields':['span','generated_from_span','statement id only when its containing object also has kind/comments_before/span'],
 'normalization_rewrites':['Function row keys 142→143, 145→146, 153→154','function def_id values through the same explicit map','Fun.Regular references through the same explicit map','HashConsedValue and Deduplicated wrappers replaced by their inline content after per-capture hash-cons resolution'],
 'other_ids_or_fields':'All other IDs, constructors, opcodes, values, orderings, fields, and metadata are compared exactly.',
 'normalized_equal':not differences,'differences':differences,
 'normalized_old_sha256':hashlib.sha256(json.dumps(a,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
 'normalized_new_sha256':hashlib.sha256(json.dumps(b,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
 'normalized_rows':{'old':a,'new':b}}
(OUT/'constant-graph-comparison.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print('normalized_equal',not differences,'differences',len(differences),'old hashcons',len(olddefs),'new hashcons',len(newdefs))
if differences: print(json.dumps(differences[:20],indent=2))
