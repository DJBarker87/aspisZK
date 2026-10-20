#!/usr/bin/env python3
"""Universally parameterize callees in the complete emitted resume body."""
from pathlib import Path
import hashlib,json,re
B=Path(__file__).resolve().parents[3]
# harness -> packet -> evidence -> spend-path
raw=(B/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean').read_text()
a=raw.index('def verifier.resume\n');z=raw.index('\n/--',a);original=raw[a:z];s=original
s=s.replace('def verifier.resume\n','def verifier.resumeWithOps\n  (ops : ResumeOps)\n',1)
s,n=re.subn(r'(?m)^( +)let \(b1, _\) ←\n[\s\S]*?\bi6 \(\)',r'\1let (b1, _) ← ops.headerAny i6',s);assert n==1
match=re.search(r'(?m)^( +)let (r\d+) ←\n\s+aspis_core.r0.heap.filled[\s\S]*?^\1let (r\d+) ←\n\s+core.result.Result.map_err[\s\S]*?^\1let (cf\d+) ←',s)
assert match
allocation=match[0][:match[0].rindex('let '+match[4])]
filled_args=re.search(r'aspis_core\.field\.QM31\.Insts\.CoreMarkerCopy\s+(\w+)\s+(\w+)',allocation)
assert filled_args
replacement=match[1]+'let '+match[3]+' ← ops.filled '+filled_args[1]+' '+filled_args[2]+'\n'+match[1]+'let '+match[4]+' ←'
s=s[:match.start()]+replacement+s[match.end():]

for old,new in [('Slice.Insts.CoreCmpPartialEqArray.ne','ops.ne'),('Slice.Insts.CoreCmpPartialEqArray','slicePartialEq ops'),('verifier.checkpoint_size','ops.checkpointSize'),('transport.Variant.tag','ops.tag'),('transport.Variant.final_len','ops.finalLen'),('verifier.Reader.raw','ops.raw'),('verifier.Reader.e','ops.readE'),('verifier.Reader.k','ops.readK'),('verifier.validate_checkpoint_queries','ops.validate'),('verifier.read_checkpoint_queries','ops.readQueries'),('verifier.read_checkpoint_semantic_alpha','ops.readSemanticAlpha'),('verifier.read_checkpoint_weights','ops.readWeights'),('aspis_core.field.QM31.ZERO','ops.zeroK')]:s=s.replace(old,new)
header='''import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1Stage2
structure ResumeOps where
  checkpointSize : transport.Variant → Result Usize
  tag : transport.Variant → Result U8
  finalLen : transport.Variant → Result Usize
  eq : {T U : Type} → {N : Usize} → core.cmp.PartialEq T U → Slice T → Array U N → Result Bool
  ne : {T U : Type} → {N : Usize} → core.cmp.PartialEq T U → Slice T → Array U N → Result Bool
  headerAny : core.slice.iter.Iter U8 → Result (Bool × core.slice.iter.Iter U8)
  raw : (N : Usize) → verifier.Reader → Result (Array U8 N × verifier.Reader)
  readE : verifier.Reader → Result (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error × verifier.Reader)
  readK : verifier.Reader → Result (core.result.Result aspis_core.field.QM31 verifier.Error × verifier.Reader)
  validate : Array U32 22#usize → Result (core.result.Result Unit verifier.Error)
  zeroK : Result aspis_core.field.QM31
  filled : Usize → aspis_core.field.QM31 → Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error)
  readQueries : Slice U8 → Usize → Result (Array U32 22#usize × Usize)
  readSemanticAlpha : Slice U8 → Usize → Result (core.result.Result (Array aspis_core.field.QM31 10#usize × Usize) verifier.Error)
  readWeights : Slice U8 → Usize → alloc.vec.Vec aspis_core.field.QM31 → Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31 × Usize) verifier.Error)

def slicePartialEq (ops : ResumeOps) {T U : Type} (N : Usize)
    (inst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T) (Array U N) where
  eq := ops.eq inst
  ne := ops.ne inst

'''
out=header+s+'\nend AspisR1Stage2\n'
(B/'lean/Stage2ContinuationResumeBody.lean').write_text(out)
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
(B/'evidence/stage2-continuation-20261020/proofs/resume-body-binding.json').write_text(json.dumps(dict(generated_resume_sha256=sha(original),parameterized_whole_body_sha256=sha(s),adapter_sha256=sha(out),whole_body_preserved=True,header_any_partial_application_abstracted=True,allocation_and_error_map_composition_abstracted=allocation,scope='All callees are universally quantified typed operations; full original post-authentication decoding/reconstruction remains in the body. No axioms.'),indent=2)+'\n')
print('prepared whole resume body',len(out),'bytes')
