import R1Z.PV_Src_PortSboxStep

/-! Totality and field meaning of the actual sixteen-cell nonlinear source
loops. The proof inducts on the remaining cells and preserves untouched words. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortSboxLoop
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
variable {K : Type} [Field K] [CharP K 2147483647]

theorem initial_loop (n : Nat) (iter : core.ops.range.Range Usize)
    (state constants1 : State) (count : iter.start.val+n=16)
    (hend : iter.end.val=16) (hs : Canonical state) (hc : Canonical constants1) :
    ∃ out, poseidon2.permute_optimized_with_trace_loop0_loop0 iter state constants1 = ok out ∧
      Canonical out ∧ ∀ j : Fin 16,
        (iter.start.val ≤ j.val → liftU (K := K) out.val[j.val]! =
          R0P.poseidonPow5 (liftU state.val[j.val]! + liftU constants1.val[j.val]!)) ∧
        (j.val < iter.start.val → out.val[j.val]! = state.val[j.val]!) := by
  induction n generalizing iter state with
  | zero =>
    refine ⟨state,?_,hs,?_⟩
    · rw [poseidon2.permute_optimized_with_trace_loop0_loop0,
        BuilderBankRange.next_none iter (by omega)]
      rfl
    · intro j
      exact ⟨fun h => False.elim (by have := j.isLt;omega),fun _ => rfl⟩
  | succ n ih =>
    have hi : iter.start.val < 16 := by omega
    obtain ⟨after,hn,ha,he⟩ := BuilderBankRange.next_some iter (by omega)
    obtain ⟨x,hstep,hx,hmodel⟩ := PV_Src_PortSboxStep.initial_step (K := K)
      iter after state constants1 iter.start hi hn hs hc
    obtain ⟨out,hout,hcan,hmeaning⟩ := ih after (state.set iter.start x)
      (by rw [ha];omega) (by rw [he];exact hend)
      (canonical_set state iter.start hi x hx hs)
    refine ⟨out,by rw [hstep,hout],hcan,?_⟩
    intro j
    constructor
    · intro hj
      by_cases same : j.val=iter.start.val
      · rw [(hmeaning j).2 (by rw [ha];omega),
          BuilderRecordsArray.set_get state iter.start x j.val (by simpa using hi),if_pos same]
        simpa only [same] using hmodel
      · rw [(hmeaning j).1 (by rw [ha];omega),
          BuilderRecordsArray.set_get state iter.start x j.val (by simpa using hi),if_neg same]
    · intro hj
      rw [(hmeaning j).2 (by rw [ha];omega),
        BuilderRecordsArray.set_get state iter.start x j.val (by simpa using hi),if_neg (by omega)]

theorem final_loop (n : Nat) (iter : core.ops.range.Range Usize)
    (state constants1 : State) (count : iter.start.val+n=16)
    (hend : iter.end.val=16) (hs : Canonical state) (hc : Canonical constants1) :
    ∃ out, poseidon2.permute_optimized_with_trace_loop2_loop0 iter state constants1 = ok out ∧
      Canonical out ∧ ∀ j : Fin 16,
        (iter.start.val ≤ j.val → liftU (K := K) out.val[j.val]! =
          R0P.poseidonPow5 (liftU state.val[j.val]! + liftU constants1.val[j.val]!)) ∧
        (j.val < iter.start.val → out.val[j.val]! = state.val[j.val]!) := by
  induction n generalizing iter state with
  | zero =>
    refine ⟨state,?_,hs,?_⟩
    · rw [poseidon2.permute_optimized_with_trace_loop2_loop0,
        BuilderBankRange.next_none iter (by omega)]
      rfl
    · intro j
      exact ⟨fun h => False.elim (by have := j.isLt;omega),fun _ => rfl⟩
  | succ n ih =>
    have hi : iter.start.val < 16 := by omega
    obtain ⟨after,hn,ha,he⟩ := BuilderBankRange.next_some iter (by omega)
    obtain ⟨x,hstep,hx,hmodel⟩ := PV_Src_PortSboxStep.final_step (K := K)
      iter after state constants1 iter.start hi hn hs hc
    obtain ⟨out,hout,hcan,hmeaning⟩ := ih after (state.set iter.start x)
      (by rw [ha];omega) (by rw [he];exact hend)
      (canonical_set state iter.start hi x hx hs)
    refine ⟨out,by rw [hstep,hout],hcan,?_⟩
    intro j
    constructor
    · intro hj
      by_cases same : j.val=iter.start.val
      · rw [(hmeaning j).2 (by rw [ha];omega),
          BuilderRecordsArray.set_get state iter.start x j.val (by simpa using hi),if_pos same]
        simpa only [same] using hmodel
      · rw [(hmeaning j).1 (by rw [ha];omega),
          BuilderRecordsArray.set_get state iter.start x j.val (by simpa using hi),if_neg same]
    · intro hj
      rw [(hmeaning j).2 (by rw [ha];omega),
        BuilderRecordsArray.set_get state iter.start x j.val (by simpa using hi),if_neg (by omega)]

#print axioms initial_loop
#print axioms final_loop
end R1Z.PV_Src_PortSboxLoop
