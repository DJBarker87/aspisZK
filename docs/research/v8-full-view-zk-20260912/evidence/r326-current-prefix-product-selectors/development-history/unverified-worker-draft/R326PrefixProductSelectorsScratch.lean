import AspisV8R19.R321BatchPrefixLoopExecutionScratch

/-! Arithmetic selectors for the R321 model-only forward prefix. No claim is
made here that R321's local execution invariants hold for a source caller. -/
set_option autoImplicit false
namespace AspisV8R19.R326PrefixProductSelectors

open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R321BatchPrefixLoopExecution

noncomputable section

/-- Accumulated prefix product, indexed from the given starting position. -/
def prefixAccum (f : Nat → M31Exact) (i : Nat) : Nat → M31Exact → M31Exact
  | 0, p => p
  | n + 1, p => prefixAccum f i n p * f (i + n)

theorem prefixAccum_shift (f : Nat → M31Exact) (i n : Nat)
    (p : M31Exact) :
    prefixAccum f (i + 1) n (p * f i) =
      prefixAccum f i (n + 1) p := by
  induction n generalizing i p with
  | zero => simp [prefixAccum]
  | succ n ih =>
      simp only [prefixAccum]
      rw [ih]
      congr 1
      omega

theorem prefixValues_getElem? (f : Nat → M31Exact) (i n : Nat)
    (p : M31Exact) (j : Nat) (hj : j < n) :
    (prefixValues f i n p)[j]? =
      some (encodeBase (prefixAccum f i (j + 1) p)) := by
  induction n generalizing i p j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero => simp [prefixValues, prefixAccum]
      | succ j =>
          have hjn : j < n := by omega
          have htail := ih (i + 1) (p * f i) j hjn
          simp only [prefixValues, List.getElem?_cons_succ]
          rw [htail]
          exact congrArg some (congrArg encodeBase
            (prefixAccum_shift f i (j + 1) p))

theorem actual_output_selector (f : Nat → M31Exact) (i n : Nat)
    (p : M31Exact) (px out : alloc.vec.Vec U32)
    (hout : out.val = px.val ++ prefixValues f i n p)
    (j : Nat) (hj : j < n) :
    out.val[px.val.length + j]? =
      some (encodeBase (prefixAccum f i (j + 1) p)) := by
  rw [hout]
  rw [List.getElem?_append_right (by omega)]
  simpa [Nat.add_sub_cancel_left] using
    (prefixValues_getElem? f i n p j hj)

#print axioms prefixAccum_shift
#print axioms prefixValues_getElem?
#print axioms actual_output_selector

end
end AspisV8R19.R326PrefixProductSelectors
