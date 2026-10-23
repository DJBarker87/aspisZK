#!/usr/bin/env python3
"""Factor both original full-parent final assignments, with kernel fission gate."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
O=Path(sys.argv[1]) if len(sys.argv)>1 else D;O.mkdir(parents=True,exist_ok=True)
s=(D/'S2SdkOwnedModelV1.lean').read_text();a=s.index('def owned_stage1_body (ops : Ops)');b=s.index('\ndef owned_stage1 (ops : Ops)',a);body=s[a:b];body=body[:body.rfind('/--')].rstrip()
spans=[]
for m in re.finditer(r'(?m)^( +)let i8 :=\n\s+alloc.vec.Vec.len\n\s+val4\n',body):
 n=len(m[1]);end=m.end()+re.search(r'(?m)^ {0,'+str(n-1)+r'}\S',body[m.end():]).start()
 spans.append((m.start(),end,n))
assert len(spans)==2,spans
for a,b,n in reversed(spans):body=body[:a]+' '*n+'finish sdk3 val4 checkpoint guards1 public1 proof\n'+body[b:]
ret='Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk × LiveGuards)'
body=body.replace('def owned_stage1_body (ops : Ops)', 'def bodyWithFinish (finish : OwnedSdk → alloc.vec.Vec U8 → OwnedAccount → LiveGuards → OwnedAccount → OwnedAccount → '+ret+') (ops : Ops)',1)
head='''-- Both exact final assignment sites in the complete emitted owned SDK parent.
import S2SdkCopyAssignmentV1
import S2SdkSnapshotEquivalenceV1
import S2SdkOwnedDecodedReuseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CopyParent

def originalFinish (sdk : OwnedSdk) (output : alloc.vec.Vec U8)
    (checkpoint : OwnedAccount) (guards : LiveGuards) (public1 proof : OwnedAccount) :=
  CopyLoop.finishAssignment sdk checkpoint.data_slot output
    {guards with «public»:=some public1.data_slot,proof:=some proof.data_slot}

def loopFinish (sdk : OwnedSdk) (output : alloc.vec.Vec U8)
    (checkpoint : OwnedAccount) (guards : LiveGuards) (public1 proof : OwnedAccount) :=
  CopyLoop.finishLoop sdk checkpoint.data_slot output
    {guards with «public»:=some public1.data_slot,proof:=some proof.data_slot}

theorem finish_eq : loopFinish=originalFinish := by
  funext sdk output checkpoint guards public1 proof
  exact CopyLoop.finish_eq sdk checkpoint.data_slot output _

'''
tail='''

/-- Kernel-checked fission of both complete original sites; all error
continuations and every SDK/guard field remain in the parent. -/
theorem body_factor (ops : Ops) (program : Array U8 32#usize)
    (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards=
      bodyWithFinish originalFinish ops program sdk data guards := by
  snapshot_defeq

/-- The count proof replaces the actual final-assignment premise in the
complete reference body, with no slot/length/loop-success premise added. -/
theorem body_eq_loop (ops : Ops) (program : Array U8 32#usize)
    (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards=
      bodyWithFinish loopFinish ops program sdk data guards := by
  rw [body_factor,finish_eq]

def stage1 (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk) := do
  let (status,heap,guards) ← bodyWithFinish loopFinish ops program sdk
    (alloc.vec.Vec.deref data) {checkpoint:=none,«public»:=none,proof:=none}
  let finalHeap ← owned_release_guards heap guards
  ok (status,finalHeap)

/-- Complete stage1 equality includes all return statuses and final cleanup. -/
theorem stage1_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) : stage1 ops program sdk data=owned_stage1 ops program sdk data := by
  unfold stage1 owned_stage1
  rw [←body_eq_loop]

#print axioms finish_eq
#print axioms body_factor
#print axioms body_eq_loop
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.CopyParent
'''
(O/'S2SdkCopyParentV1.lean').write_text(head+body+'\n'+tail)
