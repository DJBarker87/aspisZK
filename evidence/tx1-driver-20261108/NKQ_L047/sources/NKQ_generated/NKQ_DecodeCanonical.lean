import NKQ_CanonicalBridge
set_option autoImplicit false
namespace AspisR1.NKQ_DecodeCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation ClaimsUnrolledFinish

def MainRowCanon {n : Usize} (a : Array MainQM n) : Prop := ∀ q∈a.val,NKQ_MaskCuts.Canon q
def ParentRowCanon {n : Usize} (a : Array ParentQM n) : Prop := ∀ q∈a.val,NKQ_MaskCuts.Canon (toMainQM q)

theorem main {n : Usize} (record : r1_wire.ValidatedRecord) (off : Usize)
 (out : Array MainQM n)
 (call : AspisS1ExtractedRoundChildren.decodeMain n record off=ok (.Ok out)) : MainRowCanon out := by
 intro value member
 obtain ⟨i,hi,same⟩:=List.mem_iff_getElem.mp member
 have canonical:=JFv_DecodeCanonical.source record off out call ⟨i,by simpa only [out.property] using hi⟩
 rw [←same]
 exact (NKQ_CanonicalBridge.canonical _).mp canonical

theorem parent (record : AspisR1ClaimsUnrolledParent.Record) (off : Usize)
 (out : AspisR1ClaimsUnrolledParent.Row)
 (call : sourceDecode 29#usize record off=ok (.Ok out)) : ParentRowCanon out := by
 cases decoded : AspisS1ExtractedRoundChildren.decodeMain 29#usize (toMainRecord record) off with
 | fail e => simp only [sourceDecode,decoded] at call;cases call
 | div => simp only [sourceDecode,decoded] at call;cases call
 | ok reply =>
   cases reply with
   | Err e => simp only [sourceDecode,decoded] at call;cases call
   | Ok row =>
     have same : fromMainArray row=out := core.result.Result.Ok.inj (Result.ok.inj (by simpa only [sourceDecode,decoded] using call))
     subst out
     intro value member
     change value∈row.val.map fromMainQM at member
     obtain ⟨original,member,rfl⟩:=List.mem_map.mp member
     have canonical:=main (toMainRecord record) off row decoded original member
     simpa only [fromMainQM,toMainQM] using canonical
#print axioms main
#print axioms parent
end AspisR1.NKQ_DecodeCanonical
