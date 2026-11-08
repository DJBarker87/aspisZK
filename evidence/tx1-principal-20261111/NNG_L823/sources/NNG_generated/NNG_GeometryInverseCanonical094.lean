import NFN_GeometryPart08
set_option autoImplicit false
namespace AspisR1.NNG_GeometryInverseCanonical094
open Aeneas.Std
open S7Kani2PrefixLoop (wordMul)
/-- Symbolic reverse-window induction. Each written word is a reduced
product; every other initialized word is retained by the native frame law. -/
theorem reverse (flat prefixes : List U32) {n : Nat} {inverse final : List U32}
 {suffix finalSuffix : U32} {calls : List (U32 × U32)}
 (trace : NFN_NEW_GeometryReverse.Trace flat prefixes n inverse suffix final finalSuffix calls)
 (canonical : ∀ x∈inverse,x.val<2147483647) : ∀ x∈final,x.val<2147483647 := by
 revert canonical
 induction trace with
 | done inverse suffix=>intro canonical;exact canonical
 | step n inverse next final suffix finalSuffix calls active size windows tail ih=>
   intro canonical
   apply ih
   intro x member
   obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp member
   have old : j<inverse.length := by omega
   have point := windows j old
   by_cases same : j=n
   · rw [if_pos same,List.getElem?_eq_getElem hj] at point
     have equal := Option.some.inj point
     rw [equal]
     unfold wordMul
     exact Nat.mod_lt _ (by decide)
   · rw [if_neg same,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem old] at point
     rw [Option.some.inj point]
     exact canonical _ (List.getElem_mem old)
#print axioms reverse
end AspisR1.NNG_GeometryInverseCanonical094
