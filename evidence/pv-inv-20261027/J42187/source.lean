import R1Z.PV_Inv_CompressTuple
import R1Z.PV_Inv_RegistryNoPole
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativeRegistry
open R0P R0Z.HonestValidity
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitNativeQ48 (source)
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

theorem producer (t : Trace QM31Exact) (lambda chi : Old.Q)
    (hl : Canonical lambda) (hc : Canonical chi) (tag : U32) (htag : tag.val < AspisCircleGroupOrder.P)
    (limbs : Fin 16 → U32) (link : CopyLink) (member : link ∈ copyLinks)
    (active : CopyActiveRow link.producer.row) (safe : NoPole t (decode lambda) (decode chi))
    (input_join : PV_Inv_WordTuple.tuple tag limbs=
      copyEndpointTuple t link.tag link.producer) :
    ∃ slot operand inv : Old.Q,
      PV_Inv_NativeCompress.loop (source lambda) (source (PV_Inv_EmbedTag.liftWord tag))
        (source lambda) (List.ofFn limbs)=ok (source slot) ∧
      Canonical slot ∧ field.QM31.sub (source chi) (source slot)=ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧ field.QM31.is_zero (source operand)=ok false ∧
      kernels.inverse_q (source operand)=ok (some (source inv)) ∧ Canonical inv := by
  obtain ⟨slot,hcomp,hcs,hvs⟩ := PV_Inv_CompressTuple.compress_exact lambda hl tag htag limbs
  rw [input_join] at hvs
  have hn : decode chi ≠ decode slot := by
    rw [hvs]
    exact PV_Inv_RegistryNoPole.producer t (decode lambda) (decode chi) link member active safe
  obtain ⟨d,inv,hd,hcd,hnd,ht,hi,hci⟩ := PV_Inv_NativeQ.subtract_nonzero chi slot hc hcs hn
  exact ⟨slot,d,inv,hcomp,hcs,hd,hcd,hnd,ht,hi,hci⟩

#print axioms producer
end R1Z.PV_Inv_NativeRegistry
