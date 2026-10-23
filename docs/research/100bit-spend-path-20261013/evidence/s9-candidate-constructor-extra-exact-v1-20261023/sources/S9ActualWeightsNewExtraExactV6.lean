import AspisR1S9ActualWeightsNewBoxNewV1.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1S9ActualWeightsNewBoxNewV1

namespace AspisR1S9ActualWeightsNewExtraExactV6

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- On a successful constructor run, `extra` is exactly the two values
returned by the constructor's actual fixed-index reads from `alpha`. The
array reads are retained as same-run equations, not supplied independently. -/
theorem weights_new_extra_exact_v6
    (variant : Variant)
    (alpha : Array field.QM31 (10#usize))
    (z : Array circle.SecureCirclePoint (2#usize))
    (w : Weights)
    (hnew : weights_new variant alpha z = .ok (core.result.Result.Ok w)) :
    ∃ q8 q9,
      Array.index_usize alpha 8#usize = .ok q8 ∧
      Array.index_usize alpha 9#usize = .ok q9 ∧
      w.extra = Array.make 2#usize [q8, q9] := by
  unfold weights_new at hnew
  obtain ⟨points, hpoints, hnew⟩ :=
    bind_success_inv (state_only_prefix.r0.statement_points alpha) _ _ hnew
  obtain ⟨q8, hread8, hnew⟩ :=
    bind_success_inv (Array.index_usize alpha 8#usize) _ _ hnew
  obtain ⟨q9, hread9, hnew⟩ :=
    bind_success_inv (Array.index_usize alpha 9#usize) _ _ hnew
  simp only [bind_tc_ok] at hnew
  obtain ⟨factors1, hfactor1, hnew⟩ :=
    bind_success_inv
      (weights_new_loop0 { start := 0#usize, «end» := 3#usize } points
        (Array.repeat 5#usize (Array.repeat 5#usize
          (Array.repeat 4#usize field.QM31.ZERO))))
      _ _ hnew
  obtain ⟨factors2, hfactor2, hnew⟩ :=
    bind_success_inv
      (weights_new_loop1 { start := 0#usize, «end» := 2#usize } z factors1)
      _ _ hnew
  have hinner0 := Result.ok.inj hnew
  have hinner := core.result.Result.Ok.inj hinner0
  exact ⟨q8, q9, hread8, hread9,
    (congrArg Weights.extra hinner).symm⟩

#print axioms weights_new_extra_exact_v6

end AspisR1S9ActualWeightsNewExtraExactV6
