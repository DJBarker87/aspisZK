import NCE_OpeningRead
import MultiproofConePhysicalLevels

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_CarrierEffects
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Explicit same-caller annotation of an EXISTING effect program. Each actual
reply is appended before its continuation. This is a semantic lift, not a
replacement native interpreter, source certificate or native premise discharge. -/
def annotate {A : Type} (update : reference.Scratch → A → reference.Scratch) :
    Carrier → Program Bytes State A → Program Bytes State (A × Carrier)
  | caller,.done result => .done (result,{caller with scratch:=update caller.scratch result})
  | caller,.ask input next => .ask input fun reply =>
      annotate update {caller with log:=caller.log++[(input,reply)]} (next reply)

/-- Full chronological effect and final caller of that SAME program. No
independent prefix/result/state witness is introduced. -/
theorem annotate_eval {A : Type} (update : reference.Scratch → A → reference.Scratch)
    (H : Bytes → State) (program : Program Bytes State A) (caller : Carrier) :
    eval H (annotate update caller program) =
      let out := eval H program
      (out.1,(out.2,{caller with scratch:=update caller.scratch out.2,log:=caller.log++out.1})) := by
  induction program generalizing caller with
  | done result => simp only [annotate,eval,List.append_nil]
  | ask input next ih =>
    simp only [annotate,eval,ih,List.singleton_append,List.append_assoc]

/-- In particular, the whole caller's immutable fields and rejected prefixes
are retained by the semantic annotation; no digest reply is recomputed. -/
theorem annotate_frame {A : Type} (update : reference.Scratch → A → reference.Scratch)
    (H : Bytes → State) (program : Program Bytes State A) (caller : Carrier) :
    let out := eval H (annotate update caller program)
    out.2.2.prepared = caller.prepared ∧ out.2.2.proof = caller.proof ∧
    out.2.2.log = caller.log++out.1 := by
  rw [annotate_eval]
  exact ⟨rfl,rfl,rfl⟩

def rowScratch (before : reference.Scratch) : Result reference.Row → reference.Scratch
  | .ok (.Stop after) => after
  | .ok (.Next after _ _) => after
  | _ => before

abbrev Node := Carrier → Slice U8 → Usize → Usize →
  Program Bytes State (Result reference.Row × Carrier)

/-- Complete prospective ONE-binary-iteration native fact, with SAME caller,
actual physical nodes/cursors and all chronological replies. It is not a
whole level/verifier/tree result. Source hash-selection and byte-store cuts
must discharge this statement; the current packet has not done that. -/
def NCE_Native_Row (H : Bytes → State) (native : Node) : Prop :=
  ∀ caller physical i w, physical.val.length ≤ 5504 →
    MultiproofConeNodeDomain.RowDomain physical caller.scratch i w → i.val < caller.scratch.n.val →
    eval H (native caller physical i w) =
      eval H (annotate rowScratch caller (MultiproofConePhysicalTransport.transport
        (MultiproofConePhysicalProgram.node caller.scratch physical i w)))

/-- The native row cut includes exterior caller identity and every attempted
read, including zero-read short rejection, without a whole-carrier Kani run. -/
theorem native_row_frame (H : Bytes → State) (native : Node) (cut : NCE_Native_Row H native)
    (caller : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504)
    (domain : MultiproofConeNodeDomain.RowDomain physical caller.scratch i w)
    (active : i.val < caller.scratch.n.val) :
    let out := eval H (native caller physical i w)
    out.2.2.prepared = caller.prepared ∧ out.2.2.proof = caller.proof ∧
      out.2.2.log = caller.log++out.1 := by
  rw [cut caller physical i w size domain active]
  exact annotate_frame rowScratch H _ caller

#print axioms annotate_eval
#print axioms annotate_frame
#print axioms native_row_frame
end AspisR1.NCE_CarrierEffects
end
