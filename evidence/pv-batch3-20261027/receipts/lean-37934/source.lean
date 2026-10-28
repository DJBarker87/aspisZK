import PV_B3_EvalFinite222
namespace PV_B3_EvalList222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

def read (weights : host_multilinear.SparseWeights) (i : Nat) : Result (Usize × Q) :=
  match weights.data.val[i]? with
  | none => fail Error.arrayOutOfBounds
  | some x => ok x

def steps (column : Slice Q) (weights : host_multilinear.SparseWeights) :
    Nat → Nat → Q → Result Q
  | 0, _, sum => ok sum
  | n+1, i, sum => do
    let (row,weight) ← read weights i
    let q ← Slice.index_usize column row
    let product ← aspis_core.field.QM31.mul weight q
    let next ← aspis_core.field.QM31.add sum product
    steps column weights n (i+1) next

theorem read_source (weights : host_multilinear.SparseWeights) (i : Usize) :
    host_multilinear.sparse_weight_at weights i = read weights i.val := by
  simp only [host_multilinear.sparse_weight_at, Array.index_usize, Array.getElem?_Usize_eq, read]
  rfl

theorem bounded (column : Slice Q) (weights : host_multilinear.SparseWeights) :
    ∀ n (sum : Q) (i : Usize), i.val ≤ weights.len.val →
      weights.len.val-i.val = n →
      PV_B3_BoundedLoop.bounded (PV_B3_EvalFinite222.body column weights) n (sum,i) =
        steps column weights n i.val sum := by
  intro n
  induction n with
  | zero =>
    intro sum i hi hn
    have stop : ¬ i < weights.len := by change ¬ i.val < weights.len.val; omega
    simp only [PV_B3_BoundedLoop.bounded, PV_B3_EvalFinite222.body,
      host_multilinear.multilinear_evaluate_qm31_loop.body, if_neg stop, steps]
  | succ n ih =>
    intro sum i hi hn
    have go : i < weights.len := by change i.val < weights.len.val; omega
    have inc := PV_B3_EvalRank222.increment i weights.len go
    simp only [PV_B3_BoundedLoop.bounded, PV_B3_EvalFinite222.body,
      host_multilinear.multilinear_evaluate_qm31_loop.body, if_pos go,
      lift, bind_tc_ok, read_source, steps]
    have dispatch (r : Result (ControlFlow PV_B3_EvalCounter222.State Q)) :
        (match r with
        | .ok (.done y) => .ok y
        | .ok (.cont y) => PV_B3_BoundedLoop.bounded (PV_B3_EvalFinite222.body column weights) n y
        | .fail e => .fail e
        | .div => .div) =
        (r >>= fun cf => match cf with
        | .done y => .ok y
        | .cont y => PV_B3_BoundedLoop.bounded (PV_B3_EvalFinite222.body column weights) n y) := by
      cases r with
      | fail e => rfl
      | div => rfl
      | ok cf => cases cf <;> rfl
    rw [dispatch]
    simp only [PV_B3_Result.bind_assoc, bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨row,weight⟩ hr
    dsimp only
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro q hq
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro product hp
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hs
    simp only [bind_tc_ok]
    rw [← inc]
    exact ih next (Usize.wrapping_add i 1#usize) (by omega) (by omega)

theorem source (column : Slice Q) (weights : host_multilinear.SparseWeights)
    (sum : Q) (i : Usize) (hi : i.val ≤ weights.len.val) :
    host_multilinear.multilinear_evaluate_qm31_loop column weights sum i =
      steps column weights (weights.len.val-i.val) i.val sum := by
  rw [PV_B3_EvalFinite222.source]
  exact bounded column weights _ sum i hi rfl

#print axioms read
#print axioms steps
#print axioms read_source
#print axioms bounded
#print axioms source
end PV_B3_EvalList222
