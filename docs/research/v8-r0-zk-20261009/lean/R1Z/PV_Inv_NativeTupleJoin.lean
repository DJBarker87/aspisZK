import R1Z.PV_Inv_RawBankTuple
import R1Z.PV_Inv_TaggedBank
import R1Z.PV_Inv_WordTuple
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativeTupleJoin
open Aeneas Aeneas.Std Result
open ProverCommitM31Ops48
open ProverCommitScalar48 (embed)
open AspisR1.ExtractedCurrentQM31Exact (QM31Exact)
open R0P PV_Inv_BankSource PV_Inv_BankPattern PV_Inv_RawBankRead

theorem input_join (b : Banks U32) (hb : CanonicalBanks b) (t : Trace QM31Exact)
    (bank_join : BankJoin (banks b) t) (e : CopyEndpoint) (modelTag : Nat) (tag : U32) (tag_value : embed tag = (modelTag : QM31Exact))
    (ls : Fin 16 → Limb U32) (hl : ∀ i, CanonicalLimb (ls i))
    (descriptor_join : ∀ i, limb (ls i) = (descriptor (K := QM31Exact) e).limbs i) :
    ∃ words : Fin 16 → U32,
      PV_Inv_RawBankList.reads b (List.ofFn ls)=ok (List.ofFn words) ∧
      (∀ i, canonical (words i)) ∧
      PV_Inv_WordTuple.tuple tag words = copyEndpointTuple t modelTag e := by
  obtain ⟨words,hr,hc,hv⟩ := PV_Inv_RawBankTuple.tuple_read b hb ls hl
  refine ⟨words,hr,hc,?_⟩
  change (embed tag,fun i => embed (words i)) = _
  have he : (fun i => embed (words i)) = value (banks b) (descriptor e) := by
    funext i
    rw [hv,descriptor_join]
    rfl
  rw [he,tag_value]
  exact PV_Inv_TaggedBank.source_equation (banks b) t bank_join modelTag e _ rfl

#print axioms input_join
end R1Z.PV_Inv_NativeTupleJoin
