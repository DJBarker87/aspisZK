import R1Z.PV_RW_CompressPowerFold
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressPowerChunk
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem append (lambda : Q) (n m : Nat) (power : Q) :
    PV_RW_CompressPowerFold.powerRun lambda (n+m) power=(do
      let middle ← PV_RW_CompressPowerFold.powerRun lambda n power
      PV_RW_CompressPowerFold.powerRun lambda m middle) := by
  induction n generalizing power with
  | zero => simp only [Nat.zero_add,PV_RW_CompressPowerFold.powerRun,bind_tc_ok]
  | succ n ih =>
    simp only [Nat.succ_add,PV_RW_CompressPowerFold.powerRun,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next
#print axioms append
end R1Z.PV_RW_CompressPowerChunk
