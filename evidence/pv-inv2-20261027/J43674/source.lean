import R1Z.PV_Inv_NativeTupleJoin
import R1Z.PV_Inv_TagWord
import R1Z.PV_Inv_NativeRegistry
import R1Z.PV_Inv_ActiveRegistry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_SourceProducerJoin
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitNativeQ48 (source)
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_BankPattern PV_Inv_RawBankRead

theorem source_inverse (b : Banks U32) (hb : CanonicalBanks b) (t : Trace QM31Exact)
    (bank_join : BankJoin (banks b) t) (l : CopyLink) (member : l ∈ copyLinks)
    (tag : U32) (tag_join : tag.val=l.tag)
    (ls : Fin 16 → Limb U32) (hl : ∀ i, CanonicalLimb (ls i))
    (descriptor_join : ∀ i, limb (ls i) = (descriptor (K := QM31Exact) l.producer).limbs i)
    (lambda chi : Old.Q) (hlambda : Canonical lambda) (hchi : Canonical chi)
    (safe : NoPole t (decode lambda) (decode chi)) :
    ∃ words : Fin 16 → U32, ∃ slot operand inv : Old.Q,
      PV_Inv_RawBankList.reads b (List.ofFn ls)=ok (List.ofFn words) ∧
      PV_Inv_NativeCompress.loop (source lambda) (source (PV_Inv_EmbedTag.liftWord tag))
        (source lambda) (List.ofFn words)=ok (source slot) ∧
      Canonical slot ∧ field.QM31.sub (source chi) (source slot)=ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧ field.QM31.is_zero (source operand)=ok false ∧
      kernels.inverse_q (source operand)=ok (some (source inv)) ∧ Canonical inv := by
  obtain ⟨words,hr,_,hj⟩ := PV_Inv_NativeTupleJoin.input_join b hb t bank_join l.producer l.tag tag
    (PV_Inv_TagWord.source_tag tag l.tag tag_join) ls hl descriptor_join
  have tagBound : tag.val < AspisCircleGroupOrder.P := by
    rw [tag_join]
    exact PV_Inv_ActiveRegistry.tag_bound l member
  obtain ⟨slot,operand,inv,h⟩ := PV_Inv_NativeRegistry.producer t lambda chi hlambda hchi tag tagBound words l member
    (PV_Inv_ActiveRegistry.active l member).1 safe hj
  exact ⟨words,slot,operand,inv,hr,h⟩

#print axioms source_inverse
end R1Z.PV_Inv_SourceProducerJoin
