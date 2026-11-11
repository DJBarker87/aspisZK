import NHG_Lengths
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_PublicCarrier

/-- The state carrier belongs to the SAME successful public producer. The
premise is the actual call's result, not a chosen successful serializer. -/
theorem same_execution {H : Type} (D : aspis_core.Digest32 H)
 (p : NHG_Serializer.Public) (hash : H) (root : NGX_SemanticNew.Bytes32)
 (t : r1_wire.SemanticTranscript H)
 (call : r1_semantic.public_transcript D p hash root=ok (.Ok t)) :
 ∃ bytes,p.public_bytes=ok (.Ok bytes) ∧ bytes.val.length≤1455 ∧
 r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) root=ok (.Ok t) := by
 rw [NHG_PublicTranscript.source] at call
 unfold NHG_PublicTranscript.computation at call
 rw [←NHG_Serializer.source] at call
 cases produced : p.public_bytes with
 | fail e => simp only [produced,bind_tc_fail] at call;cases call
 | div => simp only [produced,bind_tc_div] at call;cases call
 | ok result =>
   cases result with
   | Err e => simp only [produced,bind_tc_ok] at call;cases call
   | Ok bytes =>
     simp only [produced,bind_tc_ok] at call
     exact ⟨bytes,rfl,NHG_Lengths.returned p bytes produced,by rw [NGX_SemanticNew.source];exact call⟩

theorem new_carrier {H : Type} (D : aspis_core.Digest32 H)
 (hash : H) (bytes : Slice U8) (root : NGX_SemanticNew.Bytes32)
 (t : r1_wire.SemanticTranscript H)
 (call : r1_wire.SemanticTranscript.new D hash bytes root=ok (.Ok t)) :
 t.hash=hash ∧ t.next_row=0#u8 := by
 rw [NGX_SemanticNew.source] at call
 unfold NGX_SemanticNew.computation at call
 cases converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes) with
 | fail e => simp only [converted,bind_tc_fail] at call;cases call
 | div => simp only [converted,bind_tc_div] at call;cases call
 | ok result =>
   cases result with
   | Err e => simp only [converted,bind_tc_ok] at call;cases call
   | Ok n =>
     simp only [converted,bind_tc_ok] at call
     cases digested : D.digest hash (NGX_SemanticNew.parts bytes root n) with
     | fail e => simp only [digested,bind_tc_fail] at call;cases call
     | div => simp only [digested,bind_tc_div] at call;cases call
     | ok state =>
       simp only [digested,bind_tc_ok] at call
       cases call
       exact ⟨rfl,rfl⟩

theorem begin_carrier {H : Type} (D : aspis_core.Digest32 H)
 (p : NHG_Serializer.Public) (hash : H) (root : NGX_SemanticNew.Bytes32)
 (t : r1_wire.SemanticTranscript H)
 (call : r1_semantic.public_transcript D p hash root=ok (.Ok t)) :
 t.hash=hash ∧ t.next_row=0#u8 := by
 obtain ⟨bytes,_,_,source⟩:=same_execution D p hash root t call
 exact new_carrier D hash _ root t source

#print axioms same_execution
#print axioms new_carrier
#print axioms begin_carrier
end AspisR1.NHG_PublicCarrier
