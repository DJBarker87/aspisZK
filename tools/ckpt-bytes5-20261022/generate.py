#!/usr/bin/env python3
"""Reify the retained resume instruction schedule, leaving the pure tail intact."""
from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Stage2ContinuationResumeBody.lean').read_text()
body=s.split('  := do\n',1)[1].rsplit('\nend AspisR1Stage2',1)[0].rstrip()
cut=body.index('                  let b4 ←')
prefix=body[:cut]
tail=body[cut:]
lines=prefix.splitlines()
out=[]
i=0
while i<len(lines):
    line=lines[i]
    if '←' in line:
        left,right=line.split('←',1)
        indent=len(line)-len(line.lstrip())
        rhs=[right.strip()]
        i+=1
        while i<len(lines) and len(lines[i])-len(lines[i].lstrip())>indent:
            rhs.append(lines[i])
            i+=1
        expr='\n'.join(rhs)
        if 'aspis_coredigestDigest32Inst.digest hash' in expr:
            expr=expr.replace('aspis_coredigestDigest32Inst.digest hash','read')
            out.append(left+'← '+expr)
        else:
            out.append(left+'← liftResult ('+expr+')')
        continue
    out.append(line.replace('then ok (','then pure ('))
    i+=1
out.append('                  liftResult (tail ops bytes v i4 end1 s6 a2)')
text='''import CheckpointBytes5Effect
/-! Mechanical lift of the retained resume body. Each non-digest instruction
is unchanged, in order. The digest-free decoder tail is lifted as one Result.
`source` below checks this reconstruction in the kernel. -/
set_option autoImplicit false
namespace AspisR1.CheckpointBytes5Resume
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1Stage2 CheckpointBytes5Effect

'''+ '''def tail (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Digest) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+ '\n'.join(x[16:] for x in tail.splitlines())+'''

def program (ops : ResumeOps) (bytes proof public1 : Slice U8)
    (v : transport.Variant) : Code (core.result.Result
      (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+ '\n'.join(out)+'''

private theorem if_tail {A : Type} (p : Prop) [Decidable p] (a b c : A)
    (h : b = c) : (if p then a else b) = (if p then a else c) := by rw [h]

theorem source (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H) :
    erase D hash (program ops bytes proof public1 v) =
      verifier.resumeWithOps ops D bytes proof public1 v hash := by
  simp only [program,erase_bind,erase_lift,erase_read,erase_pure,erase_ite]
  unfold verifier.resumeWithOps
  repeat
    first
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value success
    | apply if_tail
  rfl

#print axioms if_tail
#print axioms source
end AspisR1.CheckpointBytes5Resume
'''
(L/'CheckpointBytes5Resume.lean').write_text(text)
