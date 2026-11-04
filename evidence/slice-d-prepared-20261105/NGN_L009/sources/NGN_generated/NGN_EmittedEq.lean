import NGN_Emitted
import NGN_Opening
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGN_EmittedEq
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem folds (v : transport.Variant) : NGN_Emitted.folds v=transport.Variant.folds v := by
 cases v <;> rfl

/-- Exact Result/scratch equality for the canonical retarget of the newly
emitted frozen body, with every opaque callee made an explicit B field.
This is the model-side substitution, not a native realization theorem. -/
theorem source (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (old : Array aspis_core.field.WideExact 29#usize) :
 NGN_Emitted.prepared B D sem v hash old=PreparedScratchModel.prepare B D sem v hash old := by
 unfold NGN_Emitted.prepared PreparedScratchModel.prepare
 simp only [folds]
 apply NFW_Bind.same; intro state
 apply NFW_Bind.same; intro start
 apply NFW_Bind.same; rintro ⟨gamma,t1⟩
 simp only [Aeneas.Std.uncurry]
 apply NFW_Bind.same; intro bytes
 apply NFW_Bind.same; intro payload
 apply NFW_Bind.same; rintro ⟨kappa,t2⟩
 simp only [Aeneas.Std.uncurry]
 apply NFW_Bind.same; rintro ⟨alpha0,t3⟩
 simp only [Aeneas.Std.uncurry]
 apply NFW_Bind.same; intro count
 split <;> simp only [bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry]
 all_goals rfl

/-- The emitted frozen body and the staged model share every intermediate
carrier. No native-output equality is introduced as a success premise. -/
theorem staged (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (old : Array aspis_core.field.WideExact 29#usize) :
 NGN_Emitted.prepared B D sem v hash old=
 (do let o ← NGN_Opening.seedCut B D sem v hash; NGN_Cuts.queryCut B D sem v old o) := by
 rw [source,NGN_Opening.source]
#print axioms folds
#print axioms source
#print axioms staged
end AspisR1.NGN_EmittedEq
