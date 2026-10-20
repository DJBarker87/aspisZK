import Aeneas
import AspisR1Stage2QueryTailCut.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1Stage2QueryTailCut

abbrev OpeningOp := (Slice Std.U8) → Std.Usize → Result (Slice Std.U8)
abbrev FourDotsOp := (Slice Std.U8) →
  (Array aspis_core.field.WideExact 29#usize) →
  Result (Array aspis_core.field.WideExact 4#usize)

def query_values_forward_prefix_ops
  (openingOp : OpeningOp) (fourDotsOp : FourDotsOp)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
  Result (core.result.Result
    (Std.Usize × Std.Usize × (Slice Std.U8) ×
      (Array aspis_core.field.WideExact 4#usize)) verifier.Error) := do
  let i ← Array.index_usize p.queries a.next
  let u ← lift (UScalar.cast .Usize i)
  let q ← openingOp proof a.next
  let dots ← fourDotsOp q g
  ok (core.result.Result.Ok (a.next, u, q, dots))

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem query_values_forward_prefix_ops_success
  (openingOp : OpeningOp) (fourDotsOp : FourDotsOp)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
  (out : core.result.Result
    (Std.Usize × Std.Usize × (Slice Std.U8) ×
      (Array aspis_core.field.WideExact 4#usize)) verifier.Error)
  (h : query_values_forward_prefix_ops openingOp fourDotsOp proof p a g obs geometry pending = .ok out) :
  ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
    (dots : Array aspis_core.field.WideExact 4#usize),
    Array.index_usize p.queries a.next = .ok i ∧
    lift (UScalar.cast .Usize i) = .ok u ∧
    openingOp proof a.next = .ok q ∧
    fourDotsOp q g = .ok dots ∧
    out = core.result.Result.Ok (a.next, u, q, dots) := by
  unfold query_values_forward_prefix_ops at h
  rcases bind_ok_inv h with ⟨i, hi, h⟩
  rcases bind_ok_inv h with ⟨u, hu, h⟩
  rcases bind_ok_inv h with ⟨q, hq, h⟩
  rcases bind_ok_inv h with ⟨dots, hdots, h⟩
  refine ⟨i, u, q, dots, hi, hu, hq, hdots, ?_⟩
  exact (Result.ok.inj h).symm

end AspisR1Stage2QueryTailCut

#print axioms AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops_success
