#!/usr/bin/env python3
"""Reconstruct the V3 extraction-harness Funs source from the pinned Aeneas output."""
from pathlib import Path
import argparse, hashlib, json, difflib

p=argparse.ArgumentParser()
p.add_argument('--original',type=Path,required=True)
p.add_argument('--adapted',type=Path,required=True)
p.add_argument('--original-types',type=Path,required=True)
p.add_argument('--adapted-types',type=Path,required=True)
p.add_argument('--model',type=Path,required=True)
p.add_argument('--model-object',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
def sha(f): return hashlib.sha256(f.read_bytes()).hexdigest()
def strip_resource(s):
    return s.replace('set_option maxHeartbeats 1000000\n','').replace('set_option maxRecDepth 2048\n','')
expected=strip_resource(a.original.read_text())
repls=[
 ('(T : Type) : core.iter.traits.iterator.Iterator\n  (core.slice.iter.ChunksExactMut T) (Slice T) := {', '(T : Type) : P6ToBytes.StdModel.MutableIterator\n  (core.slice.iter.ChunksExactMut T) (Slice T) := {'),
 ('core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next','P6ToBytes.StdModel.zipNext'),
 ('core.iter.traits.iterator.Iterator.zip.trait_default','P6ToBytes.StdModel.MutableIterator.zip.trait_default'),
]
counts=[]
for old,new in repls:
    n=expected.count(old)
    if n != 1: raise SystemExit(f'expected one occurrence, found {n}: {old}')
    expected=expected.replace(old,new)
    counts.append({'old':old,'new':new,'count':n})
actual=a.adapted.read_text()
if expected != actual:
    d=''.join(difflib.unified_diff(expected.splitlines(True),actual.splitlines(True),fromfile='expected',tofile='actual'))
    a.out.mkdir(parents=True,exist_ok=True); (a.out/'mismatch.diff').write_text(d)
    raise SystemExit('adapted Funs differs outside exact whitelist; mismatch.diff written')
if strip_resource(a.original_types.read_text()) != a.adapted_types.read_text():
    raise SystemExit('adapted Types differs beyond resource-option removals')
report={
 'result':'PASS',
 'original_generated_Funs':{'path':str(a.original),'sha256':sha(a.original)},
 'adapted_Funs':{'path':str(a.adapted),'sha256':sha(a.adapted)},
 'resource_lines_removed':['set_option maxHeartbeats 1000000','set_option maxRecDepth 2048'],
 'exact_whitelist':counts,
 'conclusion':'to_limbs, loop body, loop wrapper and outer method are unchanged by exact source reconstruction; only listed harness-interface substitutions and resource-line removal differ.',
 'original_generated_Types':{'path':str(a.original_types),'sha256':sha(a.original_types)},
 'adapted_Types':{'path':str(a.adapted_types),'sha256':sha(a.adapted_types)},
 'corrected_P6_model':{'path':str(a.model),'sha256':sha(a.model),'object_sha256':sha(a.model_object),'writeback':'uses captured chunk start'},
 'scope_limit':'This is a source adapter check, not a proof of Rust standard-library correspondence or production equivalence.'}
a.out.mkdir(parents=True,exist_ok=True)
(a.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
