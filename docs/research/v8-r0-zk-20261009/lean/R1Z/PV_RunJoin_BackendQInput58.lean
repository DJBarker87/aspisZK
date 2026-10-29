import R1Z.PV_RunJoin_BackendFillPure58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendQInput58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58
abbrev Q := aspis_core.field.QM31

def embed (q : Q) : W := ProverRwDictionaryTower.fromW
  (ProverCommitNativeOps47.embedded (ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw q)))

def element (q : Array Q 1024#usize) (j : Nat) : Q :=
  q.val[j%1024]'(by rw [q.property];exact Nat.mod_lt _ (by decide))

def values (q : Array Q 1024#usize) (j : Nat) : W := embed (element q j)

theorem read (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (q : Array Q 1024#usize) (row : Usize) (hi : row.val<1024) :
    (do let x ← Array.index_usize q row
        @aspis_core.field.wide_exact.WideExact.from_qm31 (types base) (selected base heap box ops) x)=
      ok (values q row.val) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok q row hi]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_SemanticEmbed50.complete base heap box ops]
  simp only [values,element,Nat.mod_eq_of_lt hi,embed]

#print axioms read
end R1Z.PV_RunJoin_BackendQInput58
