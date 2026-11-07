import NNH_Tx2ModelSlots
set_option autoImplicit false
noncomputable section
namespace NNH_PoolValuePorts
open Aeneas Aeneas.Std AdapterRw

/-- The scan's returned Ok evaluator determines the actual source Result.
The fallback is an Err, so neither a failed nor diverging source is inferred
to return. This is precisely the A2 direction, with no Err requirement. -/
theorem scan_ok (b : Slice U8) (after : LIBB_PoolCarriers.Afterstate) (n : Nat)
 (ok : LIBB_PoolScan.evaluator (LIB_Carriers.bytes b)=.ok (after,n)) :
 ∃ scanned, AspisR1.NFY_JHf_Scan.source b=.ok (.Ok scanned) ∧
  scanned.candidate_afterstate=after ∧ scanned.proof_length.val=n := by
 unfold LIBB_PoolScan.evaluator at ok
 rw [dif_pos (LIBB_Bytes.bytes_bound b),LIBB_Bytes.from_bytes] at ok
 cases source : AspisR1.NFY_JHf_Scan.source b with
 | fail e => simp only [source,LIBB_ModelGraph.value,LIBB_PoolScan.reply,NMS_R2N_RSLError.reply] at ok; cases ok
 | div => simp only [source,LIBB_ModelGraph.value,LIBB_PoolScan.reply,NMS_R2N_RSLError.reply] at ok; cases ok
 | ok reply => cases reply with
   | Err e => simp only [source,LIBB_ModelGraph.value,LIBB_PoolScan.reply,NMS_R2N_RSLError.reply] at ok; cases ok
   | Ok scanned =>
     simp only [source,LIBB_ModelGraph.value,LIBB_PoolScan.reply,NMS_R2N_RSLError.reply,Except.ok.injEq,Prod.mk.injEq] at ok
     exact ⟨scanned,rfl,ok⟩
#print axioms scan_ok
end NNH_PoolValuePorts
