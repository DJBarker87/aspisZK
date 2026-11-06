import NJX_DigestCut
import NKI_DigestView
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_AppendCut
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open NJX_DigestResiduals (Digest Residuals)
structure Event where
 kind : Nat
 left : NQ
 right : NQ
structure Observations where
 newEvent : Event
 emptyKind : Nat
 emptyLevel : Usize
 tweakEvent : Event
 liftEvent : Fin 8 → Event
 subEvent : Fin 8 → Event
 packKind : Fin 2 → Nat
 packArgs : Fin 2 → Fin 4 → NQ
 mulKind : Fin 2 → Nat
 mulCache : Fin 2 → NJB_PreparedCarrier.Index → NJB_PreparedCarrier.Index → U32
 mulRight : Fin 2 → NQ
/-- Projection of the ONE arbitrary-seek local record of NKI_append_global_cut,
K001 PASS / K002 matched FAIL. Occurrences retain their source positions;
new0, empty1, right tweak16, lift/sub then packs/products19..22 or17..20.
These are ONLY native asserted fields, not child-value equations. -/
def Cut (side : Bool) (level : Usize) (high : NQ) (o : Residuals) (d : Digest)
 (targets : Digest) (cache : NP) (residual : Residuals) (packed reply : Fin 2 → NQ)
 (out : Fin 4 → NQ) (l : Observations) (calls : Nat) : Prop :=
 calls=(if side then 23 else 21) ∧
 l.newEvent.kind=3 ∧ l.newEvent.left=high ∧
 (side=true → l.emptyKind=7 ∧ l.emptyLevel=level ∧ l.tweakEvent.kind=8 ∧
  l.tweakEvent.left=FIw_ScalarArithmetic.lifted (d 7) ∧
  l.tweakEvent.right=FIw_ScalarArithmetic.lifted NJX_AppendTargets.tweak) ∧
 (∀ i,(l.liftEvent i).kind=5 ∧ (l.liftEvent i).left=FIw_ScalarArithmetic.lifted (targets i) ∧
  (l.subEvent i).kind=2 ∧ (l.subEvent i).left=o i ∧ (l.subEvent i).right=FIw_ScalarArithmetic.lifted (targets i)) ∧
 (∀ g,l.packKind g=6 ∧ l.packArgs g=NJX_DigestGroups.group residual g ∧
  l.mulKind g=4 ∧ l.mulCache g=NJB_PreparedCarrier.words cache ∧ l.mulRight g=packed g) ∧
 out=(if side then ![reply 0,reply 1,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
 else ![FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,reply 0,reply 1])

def observations (level : Usize) (high : NQ) (o : Residuals) (d targets : Digest)
 (cache : NP) (residual : Residuals) (packed : Fin 2 → NQ) : Observations :=
 {newEvent:=⟨3,high,FIq_Native.field.QM31.ZERO⟩
  emptyKind:=7
  emptyLevel:=level
  tweakEvent:=⟨8,FIw_ScalarArithmetic.lifted (d 7),FIw_ScalarArithmetic.lifted NJX_AppendTargets.tweak⟩
  liftEvent:=fun i=>⟨5,FIw_ScalarArithmetic.lifted (targets i),FIq_Native.field.QM31.ZERO⟩
  subEvent:=fun i=>⟨2,o i,FIw_ScalarArithmetic.lifted (targets i)⟩
  packKind:=fun _=>6
  packArgs:=NJX_DigestGroups.group residual
  mulKind:=fun _=>4
  mulCache:=fun _=>NJB_PreparedCarrier.words cache
  mulRight:=packed}

theorem source (side : Bool) (level : Usize) (high : NQ) (o : Residuals) (d targets : Digest)
 (cache : NP) (residual : Residuals) (packed reply : Fin 2 → NQ) :
 Cut side level high o d targets cache residual packed reply
 (if side then ![reply 0,reply 1,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
 else ![FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,reply 0,reply 1])
 (observations level high o d targets cache residual packed) (if side then 23 else 21) := by
 exact ⟨rfl,rfl,rfl,fun _=>⟨rfl,rfl,rfl,rfl,rfl⟩,fun _=>⟨rfl,rfl,rfl,rfl,rfl⟩,fun _=>⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
#print Cut
#print axioms source
end AspisR1.NKI_AppendCut
end
