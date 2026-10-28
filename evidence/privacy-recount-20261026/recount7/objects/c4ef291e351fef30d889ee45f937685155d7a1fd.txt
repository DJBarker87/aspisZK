import R1Z.PV_Src_PortSboxLoop

/-! All sixteen nonlinear cells, instantiated from the symbolic recurrence. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortSboxModel
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
variable {K : Type} [Field K] [CharP K 2147483647]

theorem initial (s c : State) (hs : Canonical s) (hc : Canonical c) : ∃ out,
    poseidon2.permute_optimized_with_trace_loop0_loop0
      {start := 0#usize, «end» := 16#usize} s c = ok out ∧
    Canonical out ∧ ∀ j : Fin 16, liftU (K := K) out.val[j.val]! =
      R0P.poseidonPow5 (liftU s.val[j.val]!+liftU c.val[j.val]!) := by
  obtain ⟨out,ho,hcan,hmodel⟩ := PV_Src_PortSboxLoop.initial_loop (K := K) 16
    {start := 0#usize, «end» := 16#usize} s c (by decide) (by decide) hs hc
  exact ⟨out,ho,hcan,fun j => (hmodel j).1 (by simp)⟩

theorem final_round (s c : State) (hs : Canonical s) (hc : Canonical c) : ∃ out,
    poseidon2.permute_optimized_with_trace_loop2_loop0
      {start := 0#usize, «end» := 16#usize} s c = ok out ∧
    Canonical out ∧ ∀ j : Fin 16, liftU (K := K) out.val[j.val]! =
      R0P.poseidonPow5 (liftU s.val[j.val]!+liftU c.val[j.val]!) := by
  obtain ⟨out,ho,hcan,hmodel⟩ := PV_Src_PortSboxLoop.final_loop (K := K) 16
    {start := 0#usize, «end» := 16#usize} s c (by decide) (by decide) hs hc
  exact ⟨out,ho,hcan,fun j => (hmodel j).1 (by simp)⟩

#print axioms initial
#print axioms final_round
end R1Z.PV_Src_PortSboxModel
