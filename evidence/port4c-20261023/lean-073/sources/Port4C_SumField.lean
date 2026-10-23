import Port4C_QueryLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_SumField
open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase
open CheckpointBytes5Output (ofK)
open S7Kani3CallerTrace (Sum)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FP := ZMod AspisCircleGroupOrder.P

def weight (sum : Sum) (i : Nat) : FK :=
  ⟨⟨(sum i 0 : FP),(sum i 1 : FP)⟩,⟨(sum i 2 : FP),(sum i 3 : FP)⟩⟩

def scalar (x : FP) : FK := ⟨⟨x,0⟩,⟨0,0⟩⟩

theorem source_words (q : AspisR1Stage2.aspis_core.field.QM31) :
    ofK q=⟨⟨(q.c0.a.val : FP),(q.c0.b.val : FP)⟩,
      ⟨(q.c1.a.val : FP),(q.c1.b.val : FP)⟩⟩ := by
  rfl

/-- Four exact row-limb updates are the actual quartic-field weight step. -/
theorem update (sum sumOut : Sum) (power : AspisR1Stage2.aspis_core.field.QM31)
    (basis : Nat → FP)
    (h : ∀ i, i<64 → ∀ k : Fin 4,
      (sumOut i k : FP)=(sum i k : FP)+
        (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK power) k).val*basis i)
    (i : Fin 64) :
    weight sumOut i.val=weight sum i.val+ofK power*scalar (basis i.val) := by
  rw [source_words]
  ext <;> simp [weight,scalar]
  · simpa only [S7Kani2OwnedRowRefinement.powerLimb,Port3_RowsInstall.toK] using h i.val i.isLt 0
  · simpa only [S7Kani2OwnedRowRefinement.powerLimb,Port3_RowsInstall.toK] using h i.val i.isLt 1
  · simpa only [S7Kani2OwnedRowRefinement.powerLimb,Port3_RowsInstall.toK] using h i.val i.isLt 2
  · simpa only [S7Kani2OwnedRowRefinement.powerLimb,Port3_RowsInstall.toK] using h i.val i.isLt 3

/-- S7's reached raw congruence determines the whole decoded field weight. -/
theorem raw_weight (old : S8OwnedP6Finish.Weights)
    (state : S7Kani2AccumulatorLoop.BatchedWeights) (sum : Sum)
    (trace : S7Kani3CallerTrace.PushTrace old state sum)
    (i : Nat) (row : S8OwnedP6ValueModel.Row) (read : state.raw.val[i]?=some row) :
    S8JoinFinishField.rawValue row=weight sum i := by
  have caller := S7Kani3CallerTrace.reached_invariant old state sum trace
  have coordinates : ∀ k : Fin 4,
      ((S8OwnedP6ValueModel.rowAt row k).val : FP)=(sum i k : FP) := by
    intro k
    have congruence := caller.congruence i row read k
    have eq := congrArg (fun n : Nat => (n : FP)) congruence
    simpa only [FP,AspisCircleGroupOrder.P,ZMod.natCast_mod] using eq
  change (⟨⟨_,_⟩,⟨_,_⟩⟩ : FK)=_
  rw [coordinates 0,coordinates 1,coordinates 2,coordinates 3]
  rfl

#print axioms source_words
#print axioms update
#print axioms raw_weight
end AspisR1.Port4C_SumField
end
