import NGN_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGN_Opening
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability NFW_PreparedControl

def foldCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (gamma kappa alpha0 : PE) (t3 : transcript.Transcript H) : Result (Opening H) := do
 let folds ← transport.Variant.folds v.variant
 if folds=2#usize then
  let capacity ← 32#usize+224#usize
  let root ← core.option.Option.unwrap v.folded_root
  let payload ← lift (Array.to_slice root)
  let b1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 capacity) payload
  let b2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 b1 v.round1
  let (alpha1,t4) ← PreparedModel.scalar B.sampling D t3 30#u8 (alloc.vec.Vec.deref b2) false
  ok ⟨gamma,kappa,Array.make 2#usize [alpha0,alpha1],t4,31#u8⟩
 else
  ok ⟨gamma,kappa,Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO],t3,30#u8⟩

def alphaCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (gamma kappa : PE) (t2 : transcript.Transcript H) : Result (Opening H) := do
 let (alpha0,t3) ← PreparedModel.scalar B.sampling D t2 29#u8 v.round0 false
 foldCut B D v gamma kappa alpha0 t3

def kappaCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (gamma : PE) (t1 : transcript.Transcript H) : Result (Opening H) := do
 let bytes ← B.sampling.toBytes v.inactive
 let payload ← lift (Array.to_slice bytes)
 let (kappa,t2) ← PreparedModel.scalar B.sampling D t1 28#u8 payload false
 alphaCut B D v gamma kappa t2

def gammaCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (start : transcript.Transcript H) : Result (Opening H) := do
 let (gamma,t1) ← PreparedModel.scalar B.sampling D start 27#u8 v.y1 true
 kappaCut B D v gamma t1

def seedCut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) : Result (Opening H) := do
 let state ← r1_wire.SemanticTranscript.impl.state D sem.transcript
 let start ← transcript.Transcript.new D hash state v.variant
 gammaCut B D v start

/-- All opening cuts share the original view and the scalars returned by their
actual predecessor, rather than independently quantified replacement locals. -/
theorem opening (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) :
 NFW_PreparedControl.opening B D sem v hash=seedCut B D sem v hash := by
 rfl

theorem source (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) :
 PreparedScratchModel.prepare B D sem v hash old=
 (do let o ← seedCut B D sem v hash; NGN_Cuts.queryCut B D sem v old o) := by
 rw [NGN_Cuts.source,opening]
#print axioms opening
#print axioms source
end AspisR1.NGN_Opening
