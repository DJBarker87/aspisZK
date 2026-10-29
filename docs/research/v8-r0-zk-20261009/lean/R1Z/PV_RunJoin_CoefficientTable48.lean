import R1Z.PV_RunJoin_CoefficientsWeight46
import R1Z.PV_RunJoin_OrderedList48
import R1Z.PV_RunJoin_BatchRowValue44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientTable48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_CoefficientsWeight46 (W Column column payload)
open ProverCommitWideOps48

theorem finite (p : Nat → Nat → W) (start n : Nat) :
    payload p start n=PV_RunJoin_OrderedList48.run (fun l => column (p l)) start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [payload,PV_RunJoin_OrderedList48.run,ih]

theorem ordered (p : Nat → Nat → W) (start n : Nat) :
    payload p start n=List.ofFn (fun i : Fin n => column (p (start+i.val))) :=
  (finite p start n).trans (PV_RunJoin_OrderedList48.complete _ start n)

theorem complete (c : Nat → Nat → Raw) :
    payload (fun l j => ProverRwDictionaryTower.fromW (source (c l j))) 0 29=
      (PV_RunJoin_BatchRowValue44.table (fun l j => c l (AspisR1.rowNat j))).val := by
  rw [ordered]
  simp only [Nat.zero_add]
  rfl
#print axioms finite
#print axioms ordered
#print axioms complete
end R1Z.PV_RunJoin_CoefficientTable48
