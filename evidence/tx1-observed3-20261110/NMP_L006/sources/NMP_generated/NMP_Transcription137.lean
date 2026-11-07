import NMP_CutAlgebra
import NLJ_ObservedInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transcription137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
abbrev P := r1_wire.Prefix
abbrev T (H : Type) := r1_wire.SemanticTranscript H
abbrev C := r1_wire.Challenges
abbrev R (H : Type) := NLJ_Observed.Out H
/-- Full typed replies and mutable transcript post-state. No child law here. -/
structure Cuts (H : Type) where
 parse : Code (core.result.Result P r1_wire.Error)
 mark0 : Code Unit
 publicTranscript : P → Code (core.result.Result (T H) r1_wire.Error)
 begin : P → T H → Code (core.result.Result C r1_wire.Error × T H)
 mark1 : Code Unit
 finish : P → T H → C → Code (R H)
/-- Frozen r1_semantic.rs:311-318, with every cut left uninterpreted. -/
def code {H : Type} (c : Cuts H) : Code (R H) := do
 let p ← c.parse
 match p with
 | .Err e => pure (.Err e)
 | .Ok p =>
  c.mark0
  let t ← c.publicTranscript p
  match t with
  | .Err e => pure (.Err e)
  | .Ok t =>
   let (r,after) ← c.begin p t
   match r with
   | .Err e => pure (.Err e)
   | .Ok ch =>
    c.mark1
    c.finish p after ch
/-- The only open child is retained explicitly at its original arguments. -/
def atInput {H : Type} (i : NLJ_Observed.Input H) : Cuts H where
 parse := PrefixAdapter.parseAccepted i.bytes
 mark0 := VerifyPrefix.mark none 0#u8
 publicTranscript := fun p => S1SemanticCode.publicTranscript i.digest i.publicValue i.hash p.c1_root
 begin := S1SemanticCode.begin i.digest
 mark1 := VerifyPrefix.mark none 1#u8
 finish := fun p t c => S1SemanticCode.finish NJM_RoundJoin.R
  (IDa_Deployed.boundaries i.reservation) i.digest i.publicValue p t c none
/-- All-input model identity, including every error and outer stopped prefix.
This is a source theorem. The native certificate must supply the cut relation. -/
theorem source {H : Type} (i : NLJ_Observed.Input H) :
 code (atInput i) = S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none := rfl
#print axioms source
end AspisR1.NMP_Transcription137
end
