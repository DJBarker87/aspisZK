import NLI_SourceEquality
import NJM_RoundsPacket
import NJM_RoundsTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_RoundsHash
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (run)
def Outcome {H : Type} (hash : H) : Result (Output H) → Prop
 | .ok reply => NJM_RoundsTransport.Frame hash reply
 | .fail _ | .div => True
/-- Hash transport follows the SAME actual returned carry. This generic
list induction never evaluates the concrete ten-round recurrence. -/
theorem chain {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (rows : List Usize) (valid : ∀ r∈rows,r.val<10) (carry : Carry H) :
 Outcome carry.2.2.hash (run (NJG_RoundsCode.chain NJM_RoundJoin.R D pre rows carry)).2 := by
 induction rows generalizing carry with
 | nil => rfl
 | cons r rest ih =>
  rw [NJM_RoundsInvariant.cons_run]
  generalize call : run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)=head
  rcases head with ⟨log,reply⟩
  cases reply with
  | fail e => trivial
  | div => trivial
  | ok reply =>
   cases reply with
   | Err e => trivial
   | Ok after =>
    have bounded : r.val<10 := valid r (by simp)
    have framed := NJM_TranscriptFrame.round D pre carry.2.2 after.2.2 carry.2.1 after.2.1 carry.1 after.1 r bounded (congrArg Prod.snd call)
    have tail := ih (fun x hx=>valid x (by simp only [List.mem_cons];exact Or.inr hx)) after
    rw [framed] at tail
    exact tail
/-- At the original parsed prefix, the complete134 source result carries
the original hash on every successful return; Err/fail/div remain separate. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) :
 Outcome before.hash (run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before)).2 := by
 obtain ⟨running,whole,_⟩:=NJM_RoundsPacket.source D bytes pre parsed before
 have sourceChain := NJM_RoundsJoin.source D bytes pre parsed sites (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,before)
 rw [←sourceChain] at whole
 rw [whole]
 exact chain D (PrefixAdapter.fromOld pre) sites (fun r h=>sites_domain r h) _
#print axioms chain
#print axioms source
end AspisR1.NLI_RoundsHash
end
