import NLV_Algebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_RunLaws
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
/-- Stateful binding keeps all attempted queries, including a terminal reply. -/
theorem bind_run {A B : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (c : Code A) (k : A → Code B) (before : SdkC_Source.Log) :
 SdkC_Source.run h (CheckpointBytes5Effect.bind c k) before =
 (match SdkC_Source.run h c before with
 | (ok a,after) => SdkC_Source.run h (k a) after
 | (fail e,after) => (fail e,after)
 | (div,after) => (div,after)) := by
 induction c generalizing before with
 | done a => rfl
 | step r f ih => cases r <;> simp only [CheckpointBytes5Effect.bind,SdkC_Source.run,ih]
 | read parts f ih =>
   cases edge : h parts <;> simp only [CheckpointBytes5Effect.bind,SdkC_Source.run,edge,ih]
theorem same {A B : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (c : Code A) (f g : A → Code B)
 (eq : ∀ a before, SdkC_Source.run h (f a) before=SdkC_Source.run h (g a) before)
 (before : SdkC_Source.Log) :
 SdkC_Source.run h (CheckpointBytes5Effect.bind c f) before =
 SdkC_Source.run h (CheckpointBytes5Effect.bind c g) before := by
 rw [bind_run,bind_run]
 cases hx : SdkC_Source.run h c before with
 | mk out after => cases out <;> simp only [eq]
#print axioms bind_run
#print axioms same
end AspisR1.NLV_RunLaws
end
