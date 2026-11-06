import NJR_Cuts
set_option autoImplicit false
namespace NJR_PayloadExt
open Aeneas Aeneas.Std
abbrev K := VTop_Stages.aspis_core.field.QM31

def words (q : K) : U32 × U32 × U32 × U32 := (q.c0.a,q.c0.b,q.c1.a,q.c1.b)
/-- The harness's complete four-word observation determines the ENTIRE K,
without canonicality or any arithmetic assumption. -/
theorem injective (x y : K) (same : words x=words y) : x=y := by
 cases x with
 | mk x0 x1 =>
  cases x0 with
  | mk xa xb =>
   cases x1 with
   | mk xc xd =>
    cases y with
    | mk y0 y1 =>
     cases y0 with
     | mk ya yb =>
      cases y1 with
      | mk yc yd =>
       simp only [words,Prod.mk.injEq] at same
       rcases same with ⟨rfl,rfl,rfl,rfl⟩
       rfl

/-- Per-cell complete field observations determine the full returned vector,
including its length. Native ownership/capacity stays in the native packet. -/
theorem vector (before after : List K) (length : after.length=before.length)
 (cells : ∀ i,i<before.length→(after[i]?).map words=(before[i]?).map words) :
 after=before := by
 apply List.ext_getElem?
 intro i
 by_cases inside : i<before.length
 · have hi : i<after.length := by omega
   have h:=cells i inside
   simp only [List.getElem?_eq_getElem inside,List.getElem?_eq_getElem hi,Option.map_some] at h
   have same:=injective _ _ (Option.some.inj h)
   rw [List.getElem?_eq_getElem inside,List.getElem?_eq_getElem hi,same]
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

#print axioms injective
#print axioms vector
end NJR_PayloadExt
