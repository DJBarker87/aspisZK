import XSe_PowerDomain
import XRt_CohortMultiply
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_BasisUpdate
abbrev Basis := Array aspis_core.field.M31 256#usize
def Canonical (b : Basis) : Prop := ∀ x∈b.val,x.val<2147483647
/-- Every basis product is canonical, without a canonical node assumption. -/
theorem multiply (x y out : aspis_core.field.M31)
 (run : aspis_core.field.M31.mul x y=ok out) : out.val<2147483647 := by
 obtain ⟨z,hz,_,_,bound⟩ := XRt_CohortMultiply.canonical_output x y
 have same := Result.ok.inj (hz.symm.trans run)
 rw [←same]
 exact bound
/-- Symbolic list update preservation; no256-cell reduction. -/
theorem list {A : Type} (P : A → Prop) (xs : List A) (i : Nat) (x : A)
 (initial : ∀ a∈xs,P a) (value : P x) : ∀ a∈xs.set i x,P a := by
 intro a ha
 rcases List.mem_or_eq_of_mem_set ha with member | same
 · exact initial a member
 · simpa only [same] using value

theorem source (b out : Basis) (i : Usize) (x : aspis_core.field.M31)
 (canonical : Canonical b) (value : x.val<2147483647)
 (run : Array.update b i x=ok out) : Canonical out := by
 unfold Array.update at run
 split at run
 · cases run
 · cases Result.ok.inj run
   exact list (fun x : U32 => x.val<2147483647) b.val i.val x canonical value
#print axioms multiply
#print axioms list
#print axioms source
end XSe_BasisUpdate
