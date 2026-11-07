import NLU_InputDomain
import NKQ_RecordDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Decode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Both actual147 caller domains are derived from this136 input's SAME
parsed prefix. Repeated getters retain the same record value; no selected
successful decoder output is supplied as a premise. -/
theorem source {H : Type} (i : NLU.Input H) (domain : NLU.InputDomain i) :
 ∃ record25 record26,
 r1_wire.Prefix.validated_record i.prefix1 25#u8=ok (.Ok record25) ∧
 r1_wire.Prefix.validated_record i.prefix1 26#u8=ok (.Ok record26) ∧
 record25.row=25#u8 ∧ record26.row=26#u8 ∧
 NKQ_RecordDomains.Ready record25 29#usize 87#usize ∧
 NKQ_RecordDomains.Ready record26 29#usize 0#usize := by
 obtain ⟨bytes,pre,parsed,same⟩:=domain.parsedPrefix
 obtain ⟨record25,get25,row25,ready25⟩:=NKQ_RecordDomains.entered bytes pre parsed
  25#u8 29#usize 87#usize (by decide) (by decide) NGO_CallerDomains.Call.extra
 obtain ⟨record26,get26,row26,ready26⟩:=NKQ_RecordDomains.entered bytes pre parsed
  26#u8 29#usize 0#usize (by decide) (by decide) NGO_CallerDomains.Call.beforeZ1
 exact ⟨record25,record26,by rw [same];exact get25,by rw [same];exact get26,row25,row26,ready25,ready26⟩
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NLU_Decode
end
