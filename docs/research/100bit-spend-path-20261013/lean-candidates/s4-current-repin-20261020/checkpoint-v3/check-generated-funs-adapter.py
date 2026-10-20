#!/usr/bin/env python3
"""Reversible byte-level check for generated FunsOpsV4 source adaptation."""
from pathlib import Path
import hashlib, json, re

HERE=Path(__file__).resolve().parent
RAW=HERE/'alternate-aeneas-v1/AspisR1FastDotsCurrent/Funs.lean'
ADAPT=HERE/'funs-v2/AspisR1FastDotsCurrent/FunsOpsV4.lean'
raw=RAW.read_text(); adapted=ADAPT.read_text()
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()

external={
 'ops.arrayFromFn':'core.array.from_fn',
 'ops.wideLimbCount':'aspis_core.field.wide_exact.WideExact.LIMB_COUNT',
 'ops.wideAdd':'aspis_core.field.wide_exact.WideExact.add',
 'ops.wideFromLimbs':'aspis_core.field.wide_exact.WideExact.from_limbs',
 'ops.wideToLimbs':'aspis_core.field.wide_exact.WideExact.to_limbs',
 'ops.m31ReduceU64':'aspis_core.field.M31.reduce_u64',
 'ops.m31FromBytes':'aspis_core.field.M31.from_le_bytes',
 'ops.qm31FromBytes':'aspis_core.field.QM31.from_le_bytes',
 'ops.ebyKNew':'fast_pairing.EbyKDot.new',
 'ops.ebyKPush':'fast_pairing.EbyKDot.push',
 'ops.ebyKFinish':'fast_pairing.EbyKDot.finish',
}
# Raw generated function names are the call sites that receive the explicit ops.
fn_names=[m.group(1) for m in re.finditer(r'(?m)^def(?:\s*\n\s*|\s+)([A-Za-z0-9_.]+)',raw)]

# Remove adapter-only operation record and audit prints.
normalized=adapted
start=normalized.index('/-- External source operations are explicit parameters, not axioms. -/')
stop=normalized.index('/-- [aspis_r1_cost_probe::fast_dots::four_dots::closure',start)
normalized=normalized[:start]+normalized[stop:]
normalized=re.sub(r'(?m)^#print axioms .*\n','',normalized)
# Remove only the added per-definition binder.
for name in sorted(fn_names,key=len,reverse=True):
 normalized=re.sub(r'(?m)^(def\s*\n\s*'+re.escape(name)+r')\n\s+\(ops : FourDotsOps\)',r'\1',normalized)
 normalized=re.sub(r'(?m)^(def '+re.escape(name)+r')\n\s+\(ops : FourDotsOps\)',r'\1',normalized)
# Remove operation fields and threaded ops in expression bodies, retaining source calls.
chunks=re.split(r'(?=^/-- )',normalized,flags=re.M)
for i,chunk in enumerate(chunks):
 if ':=' not in chunk: continue
 head,body=chunk.split(':=',1)
 for new,old in external.items(): body=body.replace(new,old)
 for name in sorted(fn_names,key=len,reverse=True):
  body=re.sub(re.escape(name)+r' ops(?![A-Za-z0-9_.])',name,body)
 # Adapter-only parentheses around two higher-order callback terms.
 for name in [
  'fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32',
  'fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact',
 ]:
  body=body.replace('('+name+')',name)
 chunks[i]=head+':='+body
normalized=''.join(chunks)
normalized=re.sub(r'\n{3,}(end AspisR1FastDotsCurrent\n)',r'\n\n\1',normalized)
# Remove precisely the two generated resource commands and template import.
normalized='\n'.join(line for line in normalized.splitlines()
 if not line.startswith('set_option maxHeartbeats ')
 and not line.startswith('set_option maxRecDepth ')
 and line.strip()!='import AspisR1FastDotsCurrent.FunsExternal')+'\n'
expected='\n'.join(line for line in raw.splitlines()
 if not line.startswith('set_option maxHeartbeats ')
 and not line.startswith('set_option maxRecDepth ')
 and line.strip()!='import AspisR1FastDotsCurrent.FunsExternal')+'\n'
if normalized!=expected:
 import difflib
 print(''.join(difflib.unified_diff(expected.splitlines(True),normalized.splitlines(True),fromfile='expected',tofile='normalized')))
 raise AssertionError('generated body differs beyond enumerated adapter operations/binders')
assert 'axiom ' not in adapted and 'sorry' not in adapted
assert 'set_option maxHeartbeats' not in adapted and 'set_option maxRecDepth' not in adapted
print(json.dumps({
 'raw_generated_sha256':sha(raw),
 'adapted_sha256':sha(adapted),
 'status':'PASS: reversible normalization equals full raw generated Funs after removing resource options/template import',
 'function_declarations_threaded':len(fn_names),
 'external_operation_substitutions':len(external),
 'added_axioms_or_sorry':False,
},indent=2))
