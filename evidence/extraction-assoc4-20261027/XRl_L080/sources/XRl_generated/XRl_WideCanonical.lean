import XRl_WideBoundary
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRl_WideCanonical
def Canonical (e : XRk_Wide) : Prop :=
  XRk_CanonicalScalar.Canonical (newQ e.c0) ∧ XRk_CanonicalScalar.Canonical (newQ e.c1)

theorem word (xs : List U32) (bound : ∀ x ∈ xs, x<2147483647#u32) (i : Nat) :
    xs[i]?.getD 0#u32 < 2147483647#u32 := by
  cases h : xs[i]? with
  | none => simp only [h,Option.getD_none]; scalar_tac
  | some x =>
    simp only [h,Option.getD_some]
    exact bound x (List.mem_of_getElem? h)

theorem q (xs : List U32) (bound : ∀ x ∈ xs,x<2147483647#u32) :
    XRk_CanonicalScalar.Canonical (XRk_q xs) := by
  exact ⟨word xs bound 0,word xs bound 1,word xs bound 2,word xs bound 3⟩

/-- The actual modeled validating constructor supplies both canonical halves.
Carrier typing alone is insufficient, as XRl_WideBoundary demonstrates. -/
theorem from_limbs (xs : Array U32 8#usize) (e : XRk_Wide)
    (run : aspis_core.field.wide_exact.WideExact.from_limbs xs=ok (some e)) : Canonical e := by
  unfold aspis_core.field.wide_exact.WideExact.from_limbs at run
  split at run
  · rename_i h
    have same := Option.some.inj (Result.ok.inj run)
    subst e
    have all : ∀ x ∈ xs.val,x<2147483647#u32 := by simpa only [List.all_eq_true] using h
    constructor
    · exact q (xs.val.take 4) (fun x member => all x (List.mem_of_mem_take member))
    · exact q (xs.val.drop 4) (fun x member => all x (List.mem_of_mem_drop member))
  · cases run
#print axioms word
#print axioms q
#print axioms from_limbs
end XRl_WideCanonical
