#!/usr/bin/env python3
"""Fission both real owned stage1 prefix comparisons, exact full-parent gate."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';O=Path(sys.argv[1]) if len(sys.argv)>1 else D;O.mkdir(exist_ok=True,parents=True)
s=(D/'S2SdkOwnedModelV1.lean').read_text();a=s.index('def owned_stage1_body (ops : Ops)');b=s.index('\ndef owned_stage1 (ops : Ops)',a);body=s[a:b];body=body[:body.rfind('/--')].rstrip()
pattern=r'ops\.op0\s+core.cmp.PartialEqU8\s+(s\d+)\s+val2';body,count=re.subn(pattern,lambda m:'prefixCmp '+m[1]+' val2',body);assert count==2,count
body=body.replace('def owned_stage1_body (ops : Ops)','def bodyWithPrefixCmp (prefixCmp : Slice U8 → Array U8 688#usize → Result Bool) (ops : Ops)',1)
head='''-- Exact fission of both installed source prefix comparisons, full SDK retained.
import S2SdkProofComparatorV1
import S2SdkSnapshotEquivalenceV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofPrefixParent

def stdCmp (bytes : Slice U8) (candidate : Array U8 688#usize) : Result Bool :=
  SourceInstallation.stdSliceArrayNe core.cmp.PartialEqU8 bytes candidate

def loopCmp (bytes : Slice U8) (candidate : Array U8 688#usize) : Result Bool :=
  ProofGate.scalarNe bytes (Array.to_slice candidate)

theorem cmp_eq : loopCmp=stdCmp := by
  funext bytes candidate
  exact ProofGate.scalarNe_eq_standard bytes (Array.to_slice candidate)

'''
tail='''

/-- Both original comparison sites, including every error continuation, are
retained. No accepted-run or size premise is required for this exact fission. -/
theorem body_factor (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards=
      bodyWithPrefixCmp (fun bytes candidate => ops.op0 core.cmp.PartialEqU8 bytes candidate)
        ops program sdk data guards := by
  snapshot_defeq

/-- The complete installed reference consumes the scalar-loop correspondence.
No prefix/tag pass, comparator success or length premise is supplied. -/
theorem body_eq_loop (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body (Installation.install ops verifierOps) program sdk data guards=
      bodyWithPrefixCmp loopCmp (Installation.install ops verifierOps) program sdk data guards := by
  rw [body_factor]
  change bodyWithPrefixCmp stdCmp _ _ _ _ _=bodyWithPrefixCmp loopCmp _ _ _ _ _
  rw [cmp_eq]

def stage1 (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk : OwnedSdk) (data : alloc.vec.Vec U8) := do
  let (status,heap,guards) ← bodyWithPrefixCmp loopCmp (Installation.install ops verifierOps)
    program sdk (alloc.vec.Vec.deref data) {checkpoint:=none,«public»:=none,proof:=none}
  let out ← owned_release_guards heap guards
  ok (status,out)

/-- Complete installed stage1 equality includes every status and final cleanup. -/
theorem stage1_eq (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk : OwnedSdk) (data : alloc.vec.Vec U8) :
    stage1 ops verifierOps program sdk data=
      owned_stage1 (Installation.install ops verifierOps) program sdk data := by
  unfold stage1 owned_stage1
  dsimp only
  rw [←body_eq_loop]
  congr 1

#print axioms cmp_eq
#print axioms body_factor
#print axioms body_eq_loop
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.ProofPrefixParent
'''
(O/'S2SdkProofPrefixParentV1.lean').write_text(head+body+'\n'+tail)
