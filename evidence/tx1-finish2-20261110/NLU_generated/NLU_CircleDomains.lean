import NLU_InputDomain
import NKQ_CircleDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Circle
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Both actual142 caller domains at the SAME parsed prefix. Universality in
the second carry permits the preceding circle's ACTUAL returned transcript;
no separate successful execution or child Result is a premise. Physical
parent slot/cut installation remains separate from this source-domain lemma. -/
theorem source {Pointer H : Type} (i : NLU.Input H) (domain : NLU.InputDomain i)
 (template : NIX_DispatchCut.Pre Pointer) (beforeFirst beforeSecond : r1_wire.SemanticTranscript H) :
 ∃ first second,
 r1_wire.Prefix.validated_record i.prefix1 25#u8=ok (.Ok first) ∧
 r1_wire.Prefix.validated_record i.prefix1 26#u8=ok (.Ok second) ∧
 first.row=25#u8 ∧ second.row=26#u8 ∧
 NJM_InvocationRoots.Circle i.digest template beforeFirst first ∧
 NJM_InvocationRoots.Circle i.digest template beforeSecond second := by
 obtain ⟨bytes,pre,parsed,samePrefix⟩:=domain.parsedPrefix
 have packet:=NKQ_CircleDomains.source i.digest template bytes beforeFirst beforeSecond
 rw [parsed] at packet
 rw [samePrefix]
 exact packet
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NLU_Circle
end
