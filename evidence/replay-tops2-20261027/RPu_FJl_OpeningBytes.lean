import RPu_FJi_QueryJoin
import Port4B_Opening
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_OpeningBytes
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft
/-- The SAME backend opening608 at a reached query has the SAME literal 608 bytes. -/
theorem value (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
    (g : Array FIp_DotsAdapter.E 29#usize) (i : Usize) (bound : i.val<22)
    (size : proof.val.length=57607) (parsed : Parsed) (wire : parsed.wire=bytesOf proof.val)
    (installed : ops.op11=Port4B_Opening.opening)
    (meaning : FJi_QueryJoin.Meaning ops proof i g) :
    ∃ (opening : Slice U8) (dots : Array FIp_DotsAdapter.E 4#usize) (opening608 : Array U8 608#usize),
      ops.op11 proof i=ok opening ∧ FIp_DotsAdapter.dots opening g=ok dots ∧
      bytesOf opening.val=OraclePortSelectedDraft.opening parsed i.val ∧
      bytesOf opening608.val=(OraclePortSelectedDraft.opening parsed i.val).take 608 ∧
      ∀ slot : Fin 4,Port5Q1_OpeningValues.values dots slot=FJi_SlotValue.model opening608
        (FIp_DotsAdapter.toArray g) (Usize.ofNat slot.val (by have:=slot.isLt; scalar_tac)) := by
  obtain ⟨opening,dots,opening608,ho,hd,hp,hv⟩ := meaning
  obtain ⟨view,read,len,bytes⟩ := Port4B_Opening.opening_exact proof size i bound
  rw [installed] at ho
  have same := Result.ok.inj (read.symm.trans ho)
  have literal : bytesOf opening.val=OraclePortSelectedDraft.opening parsed i.val := by
    rw [same,←wire] at bytes
    exact bytes
  refine ⟨opening,dots,opening608,by rwa [installed],hd,literal,?_,hv⟩
  rw [hp]
  change (opening.val.take 608).map _=_
  rw [List.map_take]
  exact congrArg (List.take 608) literal
#print axioms value
end AspisR1.FJl_OpeningBytes
end
