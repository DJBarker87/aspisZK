import NHE_Round
import NGM_WordArrayEquality
set_option autoImplicit false
noncomputable section
namespace NHE_RoundRef
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
attribute [local instance] Classical.propDecidable

theorem words_injective : Function.Injective NGM_RawWords.nativeWords := by
 intro x y same
 have stage : NGM_RawWords.words (FIo_Install.fromE x)=NGM_RawWords.words (FIo_Install.fromE y) := same
 exact NHE_Round.from_injective (NGM_RawWords.injective stage)

theorem observed (lhs rhs out : NE) :
 NGW_HelperRef.round_ref (NGM_RawWords.nativeWords lhs) (NGM_RawWords.nativeWords rhs) (NGM_RawWords.nativeWords out)=
 ok (if lhs≠rhs then core.result.Result.Err 3#u8 else .Ok (NGM_RawWords.nativeWords out)) := by
 have eq : (NGM_RawWords.nativeWords lhs≠NGM_RawWords.nativeWords rhs) ↔ lhs≠rhs :=
  not_congr ⟨fun h=>words_injective h,fun h=>congrArg NGM_RawWords.nativeWords h⟩
 simp only [NGW_HelperRef.round_ref,NGM_WordArrayEquality.arrays_ne,bind_tc_ok,eq,decide_eq_true_eq]
 split <;> rfl

#print axioms words_injective
#print axioms observed
end NHE_RoundRef
end
