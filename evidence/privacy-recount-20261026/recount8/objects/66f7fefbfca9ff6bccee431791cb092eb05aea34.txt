import R1Z.PredicateR1
import R0Z.TerminalClosed

/-! Clause (i′) on R1 (DESIGN-R1-PRIVACY-MODEL §3.6 b; LOG D30.3, D35):
under `P_R1`, the remainder `sRem` of every instance with the given public
statement is the payload of a mask tape.  Inputs: J2/J2-R1
(`sRem_mem_chain0K4`), J2b (`terminalClosed`), R1-3 (`chain0K4_le_silent_R1`,
which uses `BCondG_R1` through `bcond_of_G`).  This is the first half of
`MaskImageOn P_R1`; clause (ii′) is separate. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.ClauseIR1

open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.Shift
open R1Z.Batched R1Z.PredicateR1

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Clause (i′) at one challenge. -/
theorem clause_i_R1 (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w))
    (ch : Challenges K) (hP : P_R1 h.transport B hB ch) (w : h.Instance) (n : N K F)
    (hw : h.public w = x.1) :
    sRem (Bat := R1Bat) h B x w ch n ∈
      LinearMap.range ((A (Bat := R1Bat) h.transport B ch).comp inlM) := by
  have hK := R0Z.K4Values.sRem_mem_chain0K4 (Bat := R1Bat) h B hB x w ch n hP.2.1 (hF w hw)
    (R0Z.TerminalClosed.terminalClosed B hB x.1 ch hP.2.1 hpub) hP.1
  obtain ⟨m, _, hm⟩ := Submodule.mem_map.1 (chain0K4_le_silent_R1 hP hK)
  exact ⟨m, hm⟩

/-- Clause (i′) in the form of the first conjunct of `MaskImageOn P_R1`. -/
theorem clause_i_R1_all (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hF : ∀ w, h.public w = x.1 → BaseTyped F (h.build w)) :
    ∀ ch, P_R1 h.transport B hB ch → ∀ w n, h.public w = x.1 →
      sRem (Bat := R1Bat) h B x w ch n ∈
        LinearMap.range ((A (Bat := R1Bat) h.transport B ch).comp inlM) :=
  fun ch hP w n hw => clause_i_R1 h B hB x hpub hF ch hP w n hw

#print axioms clause_i_R1
#print axioms clause_i_R1_all

end R1Z.ClauseIR1

end
