import AuS1_Vec
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_OriginalRead
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

 theorem frame (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (input scratch : Array aspis_core.field.WideExact 29#usize) (out : verifier.Prepared)
    (root : Array U8 32#usize) (variant : view.variant = .S2) (folded : view.folded_root = some root)
    (success : erase (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash input) = ok (.Ok out,scratch)) :
    ∃ frame, Read (observe (run (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash input)).1) frame ∧
      BinRawByteCollisionTargets.pred 3 frame = some (decodeState root) := by
  obtain ⟨before,after,actual,b1,b2,alpha,hroot,hb1,hb2,scalar,contains⟩ :=
    AuS1_Row30.reached (preparationEffects B Q) D sem view hash input scratch out variant success
  rw [folded] at hroot
  change ok root = ok actual at hroot
  have same := Result.ok.inj hroot
  subst actual
  let len := UScalar.cast .U32 (Slice.len b2.deref)
  have tag : (160#u8 + 30#u8 : Result U8) = ok 190#u8 := by
    obtain ⟨out,call,fields⟩ := WP.spec_imp_exists
      (U8.add_spec (x:=160#u8) (y:=30#u8) (by scalar_tac))
    have value : out = 190#u8 := by scalar_tac
    simpa only [value] using call
  refine ⟨flatten (AuS1_Absorb.parts before.state 190#u8 len b2.deref),?_,?_⟩
  · exact contains _ (AuS1_Block.scalar_read B.sampling D before after 30#u8 190#u8 b2.deref
      len false alpha tag rfl scalar)
  · exact AuS1_Frame.folded before.state root 190#u8 len view.round1.val b2.deref
      (AuS1_Vec.payload root view.round1 b1 b2 hb1 hb2)

#print axioms frame
end AspisR1.AuS1_OriginalRead
end
