import NKE_CommonDomain
import NKE_CommonNative
set_option autoImplicit false
noncomputable section
namespace NKE_PendingAtSource
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (weights : Slice aspis_core.field.QM31) (reply : R verifier.BatchedWeights)
 (entered : Event.pending weights reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 reply=NKE_CommonNative.pendingG rr weights := by
 obtain ⟨width,same⟩ := NKE_CommonDomain.source wr rr merkle finish d pub proof ck hash
  (.pending weights reply) entered
 rw [same]
 have step := NKE_PendingNative.source rr weights (NKE_CommonNative.zeros weights) width
  (by simpa only [NKE_CommonNative.zeros,List.length_replicate] using width)
 cases rr with
 | Err error => exact step
 | Ok unit => cases unit;exact step

theorem native_rows (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (weights : Slice aspis_core.field.QM31) (reply : R verifier.BatchedWeights)
 (entered : Event.pending weights reply∈(run wr rr merkle finish d pub proof ck hash none).events) (i : Nat) (inside : i<64) :
 NJR_Cuts.pending weights
  (NKE_PendingNative.states weights (NKE_CommonNative.zeros weights) i)
  (NKE_PendingNative.states weights (NKE_CommonNative.zeros weights) (i+1)) i (i+1) := by
 obtain ⟨width,_⟩ := NKE_CommonDomain.source wr rr merkle finish d pub proof ck hash
  (.pending weights reply) entered
 exact NKE_PendingNative.cut weights (NKE_CommonNative.zeros weights) width
  (by simpa only [NKE_CommonNative.zeros,List.length_replicate] using width) i inside
#print axioms source
#print axioms native_rows
end NKE_PendingAtSource
