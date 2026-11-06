import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
/-- Every independently returned semantic Error maps to Semantic, keeps the
original scratch and never enters179. No semantic success is selected. -/
theorem error (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8)
 (v : verifier.View) (e : r1_wire.Error) :
 run (step cfg ⟨i,.mapSemantic logical v (.Err e)⟩) = ([],ok (.inl (.Err verifier.Error.Semantic,i.scratch))) := rfl
/-- Success carries the SAME complete Verified, view, logical owner and scratch. -/
theorem carry (cfg : Configuration) {H : Type} (i : Input H) (logical : alloc.vec.Vec U8)
 (v : verifier.View) (sem : r1_semantic.Verified H) :
 run (step cfg ⟨i,.mapSemantic logical v (.Ok sem)⟩) =
 ([],ok (.inr ⟨i,.mark logical v sem⟩)) := rfl
#print axioms error
#print axioms carry
end AspisR1.NLJ_Prepare
end
