import JGv_DotTotal
import Port4C_QueryArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotCanonical
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open JGv_DotOps

theorem source (fm : Slice U8) (ws : Slice AspisR1Stage2.Stage2Finish.K)
    (out : AspisR1Stage2.Stage2Finish.E)
    (length : ws.val.length=64)
    (read : ∀ i : Usize,i.val<64 → ∃ x,finishField fm i=ok x ∧ CanonicalFinish x)
    (canonical : ∀ q∈ws.val,Port3_FlushInstall.Canonical q)
    (success : SAG_DotClosed.source fm ws=ok (.Ok out)) :
    Port4C_QueryArithmetic.CanonE out := by
  have cm : ∀ q∈(SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws).val,CanonQ q := by
    intro q hq
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp hq
    have hc := canonical original member
    exact ⟨⟨hc.1,hc.2.1⟩,hc.2.2⟩
  obtain ⟨value,run,c⟩ := JGv_DotTotal.kernel fm (SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws)
    (by simpa only [SAG_DotAdapter.mapSlice,List.length_map] using length) read cm
  have mapped : SAG_DotClosed.source fm ws=ok (.Ok (SAG_DotAdapter.toStageE value)) := by
    change (do let result ← SAG_DotAdapter.kernel SAG_DotClosed.seed fm ws
               match result with
               | core.result.Result.Ok v=>ok (core.result.Result.Ok (SAG_DotAdapter.toStageE v))
               | core.result.Result.Err e=>ok (core.result.Result.Err (SAG_DotAdapter.toStageError e)))=_
    rw [show SAG_DotAdapter.kernel SAG_DotClosed.seed fm ws=ok (.Ok value) from run,bind_tc_ok]
  have same := core.result.Result.Ok.inj (Result.ok.inj (mapped.symm.trans success))
  rw [←same]
  exact ⟨⟨c.1.1.1,c.1.1.2,c.1.2.1,c.1.2.2⟩,
    ⟨c.2.1.1,c.2.1.2,c.2.2.1,c.2.2.2⟩⟩
#print axioms source
end AspisR1.JGv_DotCanonical
end
