import S4ScanOutRunCoreV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.S4TraceLiteralOutputJoinV1
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.R4Transport2QueryPrefix
open AspisR1.R4Transport2ScanComposition

/-- Join the literal row-31 sampler's same-pair result to the exact output of
    the materialized source scanner. `hviews` records only the pair-array list
    views; `htrace` is the actual `scanOut` result for those arrays. -/
theorem literal_list_eq_trace_values
    (ps : List (AspisV8R19.SourceDuplexStep.State × AspisV8R19.SourceDuplexStep.State))
    (initial : AspisV8R19.SourceDuplexStep.State)
    (xs : List Nat)
    (blocks advances : List AspisV8R19.SourceDuplexStep.State)
    (out : Array U32 22#usize) (final : AspisV8R19.SourceDuplexStep.State)
    (hlen : ps.length = 8)
    (hpairs : (pairsRun R0C.V3.Q22.q0 ps initial).1 = .ok xs)
    (hviews : ps.map Prod.fst = blocks ∧ ps.map Prod.snd = advances)
    (htrace : (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 blocks advances initial).1 =
      .ok (out.val.map (fun w => w.val))) :
    out.val.map (fun w => w.val) = xs := by
  have hr := congrArg Prod.fst (AspisR1.R4Transport2ScanComposition.eight_pairs_selected ps initial hlen)
  rw [hviews.1, hviews.2] at hr
  have hresult : (Except.ok xs : Except Nat (List Nat)) =
      Except.ok (out.val.map (fun w => w.val)) := by
    calc
      Except.ok xs = (pairsRun R0C.V3.Q22.q0 ps initial).1 := hpairs.symm
      _ = (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 blocks advances initial).1 := hr
      _ = Except.ok (out.val.map (fun w => w.val)) := htrace
  cases hresult; rfl

#print axioms literal_list_eq_trace_values
end AspisR1.S4TraceLiteralOutputJoinV1
end
