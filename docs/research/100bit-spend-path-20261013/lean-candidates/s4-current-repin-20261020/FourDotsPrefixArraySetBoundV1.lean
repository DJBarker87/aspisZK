import Aeneas
import Aeneas.Std.Array.Array
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std

namespace AspisR1FastDotsPrefixArraySetBound

abbrev U64 := UScalar UScalarTy.U64
abbrev cap : Nat := (2147483646)^2

def cell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

/-- A checked write of one canonical product preserves the uniform per-cell
    prefix bound and advances it by one product cap. -/
theorem set_advances_bound (a : Array U64 8#usize) (i : Usize) (x : U64)
    (k : Nat)
    (hbase : ∀ j : Fin 8, cell a j ≤ k * cap)
    (hnew : x.val ≤ cap) :
    ∀ j : Fin 8, cell (a.set i x) j ≤ (k + 1) * cap := by
  intro j
  have hjset : j.val < (a.val.set i.val x).length := by simpa [a.property] using j.isLt
  change ((a.val.set i.val x)[j.val]'hjset).val ≤ (k + 1) * cap
  have hstep : k * cap ≤ (k + 1) * cap := by
    have hm := Nat.mul_le_mul_right cap (Nat.succ_le_succ (Nat.zero_le k))
    simpa using hm
  have hcapStep : cap ≤ (k + 1) * cap := by
    have hm := Nat.mul_le_mul_right cap (Nat.succ_le_succ (Nat.zero_le k))
    simpa using hm
  by_cases heq : i.val = j.val
  · have hself : (a.val.set i.val x)[j.val]'hjset = x := by
      have hs := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjset)
      simpa [heq] using hs
    rw [hself]
    exact le_trans hnew hcapStep
  · have hother : (a.val.set i.val x)[j.val]'hjset = a.val[j.val]'(by simpa [a.property] using j.isLt) := by
      exact List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val) heq hjset
    rw [hother]
    have hb := hbase j
    exact le_trans hb hstep

#print axioms set_advances_bound
end AspisR1FastDotsPrefixArraySetBound
