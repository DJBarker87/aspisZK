import PV_B3_EvalList222
namespace PV_B3_EvalFold222
open Aeneas Aeneas.Std Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

def fold (column : Slice Q) : List (Usize × Q) → Q → Result Q
  | [],sum => ok sum
  | (row,weight)::xs,sum => do
    let q ← Slice.index_usize column row
    let product ← aspis_core.field.QM31.mul weight q
    let next ← aspis_core.field.QM31.add sum product
    fold column xs next

theorem steps (column : Slice Q) (weights : host_multilinear.SparseWeights) :
    ∀ n i (sum : Q), i+n ≤ weights.data.val.length →
      PV_B3_EvalList222.steps column weights n i sum =
        fold column ((weights.data.val.drop i).take n) sum := by
  intro n
  induction n with
  | zero => intro i sum hi; rfl
  | succ n ih =>
    intro i sum hi
    have hidx : i < weights.data.val.length := by omega
    rw [List.drop_eq_getElem_cons hidx, List.take_succ_cons]
    simp only [PV_B3_EvalList222.steps, PV_B3_EvalList222.read,
      List.getElem?_eq_getElem hidx, bind_tc_ok]
    rcases hpair : weights.data.val[i] with ⟨row,weight⟩
    simp only [fold]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro q hq
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro product hp
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hn
    exact ih (i+1) next (by omega)

theorem source (column : Slice Q) (weights : host_multilinear.SparseWeights)
    (sum : Q) (i : Usize) (hi : i.val ≤ weights.len.val)
    (hlen : weights.len.val ≤ 1024) :
    host_multilinear.multilinear_evaluate_qm31_loop column weights sum i =
      fold column ((weights.data.val.drop i.val).take (weights.len.val-i.val)) sum := by
  rw [PV_B3_EvalList222.source column weights sum i hi]
  apply steps
  rw [weights.data.property]
  change i.val+(weights.len.val-i.val) ≤ 1024
  omega

#print axioms fold
#print axioms steps
#print axioms source
end PV_B3_EvalFold222
