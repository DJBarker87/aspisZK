import Hir_PartialOracle
import RPz7_GExp_CountLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_PartialPrefix
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Partial syscall failure can truncate, but cannot reorder or erase the
successful prefix. This holds in every ideal oracle world without P1. -/
theorem read_prefix (hashv : Parts → Result Digest) {A : Type} (code : Code A) (H : Bytes → State) :
    (eval H (Hir_PartialOracle.program hashv code)).1 <+:
      (eval H (SdkC_Oracle.program code)).1 := by
  induction code with
  | done a => exact ⟨[], rfl⟩
  | step r k ih => cases r with
    | ok a => exact ih a
    | fail e => exact ⟨[], rfl⟩
    | div => exact ⟨[], rfl⟩
  | read parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      simp only [Hir_PartialOracle.program,SdkC_Oracle.program,actual,eval]
      obtain ⟨suffix,eq⟩ := ih (encodeState (H (flatten parts)))
      exact ⟨suffix,by simp only [List.cons_append,eq]⟩
    | fail e =>
      simp only [Hir_PartialOracle.program,actual,eval]
      exact List.nil_prefix
    | div =>
      simp only [Hir_PartialOracle.program,actual,eval]
      exact List.nil_prefix

theorem budget (hashv : Parts → Result Digest) {A : Type} (code : Code A) (n : Nat)
    (bound : GExp_CountLaws.count n code) (H : Bytes → State) :
    (eval H (Hir_PartialOracle.program hashv code)).1.length ≤ n :=
  (read_prefix hashv code H).length_le.trans (bound H)

#print axioms read_prefix
#print axioms budget
end AspisR1.Hir_PartialPrefix
end
