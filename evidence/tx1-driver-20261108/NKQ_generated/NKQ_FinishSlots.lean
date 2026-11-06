import NKQ_RecordDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_FinishSlots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation RawActualDecodeKMainAdapter

/-- The exact25/87 and26/0 calls of136. Getter, byte frame and full decoder
values are produced from the SAME parser branch, rather than supplied as
successful child observations. Terminal256 is not needed for these domains. -/
theorem source (bytes : Slice U8) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   ∃ record25 record26 extra beforeZ1,
    r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 25#u8=ok (.Ok record25) ∧
    r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 26#u8=ok (.Ok record26) ∧
    record25.row=25#u8 ∧ record26.row=26#u8 ∧
    decodeMain 29#usize record25 87#usize=ok (.Ok extra) ∧ NKQ_DecodeCanonical.MainRowCanon extra ∧
    decodeMain 29#usize record26 0#usize=ok (.Ok beforeZ1) ∧ NKQ_DecodeCanonical.MainRowCanon beforeZ1
 | _ => True := by
 split
 · rename_i pre parsed
   have size : (29#usize).val=29 := by scalar_tac
   have tail : (87#usize).val=87 := by scalar_tac
   have zero : (0#usize).val=0 := by scalar_tac
   have firstCall : NGO_CallerDomains.Call (25#u8).val (29#usize).val (87#usize).val := by
    rw [size,tail];exact NGO_CallerDomains.Call.extra
   have secondCall : NGO_CallerDomains.Call (26#u8).val (29#usize).val (0#usize).val := by
    rw [size,zero];exact NGO_CallerDomains.Call.beforeZ1
   obtain ⟨r25,g25,t25,c25,h25,s25⟩:=NKQ_RecordDomains.entered bytes pre parsed
    25#u8 29#usize 87#usize (by decide) (by decide) firstCall
   obtain ⟨r26,g26,t26,c26,h26,s26⟩:=NKQ_RecordDomains.entered bytes pre parsed
    26#u8 29#usize 0#usize (by decide) (by decide) secondCall
   obtain ⟨extra,d25,k25⟩:=NKQ_StrictDecode.total 29#usize 87#usize r25 c25 h25 s25
   obtain ⟨before,d26,k26⟩:=NKQ_StrictDecode.total 29#usize 0#usize r26 c26 h26 s26
   exact ⟨r25,r26,extra,before,g25,g26,t25,t26,d25,k25,d26,k26⟩
 · trivial
#print axioms source
#print source
end AspisR1.NKQ_FinishSlots
end
