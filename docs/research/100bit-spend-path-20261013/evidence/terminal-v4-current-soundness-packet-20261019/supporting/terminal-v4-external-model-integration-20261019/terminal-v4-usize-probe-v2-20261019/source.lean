import Aeneas
import Lean.Elab.Tactic.Omega

open Aeneas Aeneas.Std
theorem val_le_max (x : Usize) : UScalar.val x ≤ Usize.max := by
  change x.bv.toNat ≤ Usize.max
  have hlt := x.bv.isLt
  dsimp [Usize.max, Usize.rMax] at *
  omega
