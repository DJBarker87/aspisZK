import BEk_LawFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_LawCompose
open Aeneas Aeneas.Std Result SdkC_Source BEh_Scope

/-- Error-kind-independent local composition. Common projection/history must
be on the same middle cut; independently chosen source executions do not suffice. -/
theorem trans {S A E F G : Type} (left : Outcome S A E) (middle : Outcome S A F)
    (right : Outcome S A G) (first : Law left middle) (second : Law middle right) :
    Law left right := by
  apply (BEk_LawFields.exact_fields left right).mpr
  exact ⟨(BEk_LawFields.accepted_eq left middle first).trans
    (BEk_LawFields.accepted_eq middle right second),
    (logs left middle first).trans (logs middle right second),
    fun a yes => (congrArg Prod.fst (first.1.2 a yes)).trans
      (congrArg Prod.fst (second.1.2 a ((first.1.1 a).mp yes)))⟩

theorem symm {S A E F : Type} (left : Outcome S A E) (right : Outcome S A F)
    (law : Law left right) : Law right left := by
  apply (BEk_LawFields.exact_fields right left).mpr
  exact ⟨(BEk_LawFields.accepted_eq left right law).symm,(logs left right law).symm,
    fun a yes => (congrArg Prod.fst (law.1.2 a ((law.1.1 a).mpr yes))).symm⟩

#print axioms trans
#print axioms symm
end AspisR1.BEk_LawCompose
end
