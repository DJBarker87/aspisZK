import R1Z.PV_RJDec_AsmMemory
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_AsmBind
open Aeneas Aeneas.Std PV_W_Threading
variable [ProverRwFull.ExternalTypes] {W F C A : Type}
/-- The caller keeps its complete failure/divergence outcome and all calls,
following the one zeroization call and the committed post-write world. -/
theorem complete (m : PV_RJDec_AsmMemory.Memory W F) (N : Usize)
    (v : Array U8 N) (w : W)
    (k : Array U8 N → M W (Option C) Aeneas.Std.Error A) :
    PV_W_Threading.bind (PV_RJDec_AsmMemory.array m N v) k w =
      let z := m.commit w (PV_RDCD_ZeroWorld.indexed (m.arrayAddress w v) 0 N.val (m.view w))
      let r := k (Array.repeat N 0#u8) z
      ⟨r.outcome,r.world,[(w,none)] ++ r.calls⟩ := by
  unfold PV_W_Threading.bind
  rw [PV_RJDec_AsmMemory.array_complete]
#print axioms complete
end R1Z.PV_RJDec_AsmBind
