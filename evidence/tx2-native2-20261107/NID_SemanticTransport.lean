import NID_WithKTransport
set_option autoImplicit false
noncomputable section
namespace NID_SemanticTransport
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- All ten scalar calls on their actual evolving reader. The successful head
provides the next bound; a rejection never executes the suffix. -/
theorem sequence (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize)
 (bound : start.val+160≤bytes.val.length) :
 CheckpointBytes4Ops.semanticUsing (T2Nat_ScalarJoin.readK unwrap) bytes start=
 CheckpointBytes4Ops.readSemanticAlpha bytes start := by
 unfold CheckpointBytes4Ops.readSemanticAlpha CheckpointBytes4Ops.semanticUsing
 apply NID_WithKTransport.source unwrap unwrap_ok (⟨bytes,start⟩ : verifier.Reader) _ _ (by change start.val+16≤bytes.val.length;omega)
 intro x0 r1 c0
 have b1 := NID_ReadStepFrame.remaining (⟨bytes,start⟩ : verifier.Reader) r1 9 x0 (by exact bound) c0
 apply NID_WithKTransport.source unwrap unwrap_ok r1 _ _ (by omega)
 intro x1 r2 c1
 have b2 := NID_ReadStepFrame.remaining r1 r2 8 x1 (by exact b1) c1
 apply NID_WithKTransport.source unwrap unwrap_ok r2 _ _ (by omega)
 intro x2 r3 c2
 have b3 := NID_ReadStepFrame.remaining r2 r3 7 x2 (by exact b2) c2
 apply NID_WithKTransport.source unwrap unwrap_ok r3 _ _ (by omega)
 intro x3 r4 c3
 have b4 := NID_ReadStepFrame.remaining r3 r4 6 x3 (by exact b3) c3
 apply NID_WithKTransport.source unwrap unwrap_ok r4 _ _ (by omega)
 intro x4 r5 c4
 have b5 := NID_ReadStepFrame.remaining r4 r5 5 x4 (by exact b4) c4
 apply NID_WithKTransport.source unwrap unwrap_ok r5 _ _ (by omega)
 intro x5 r6 c5
 have b6 := NID_ReadStepFrame.remaining r5 r6 4 x5 (by exact b5) c5
 apply NID_WithKTransport.source unwrap unwrap_ok r6 _ _ (by omega)
 intro x6 r7 c6
 have b7 := NID_ReadStepFrame.remaining r6 r7 3 x6 (by exact b6) c6
 apply NID_WithKTransport.source unwrap unwrap_ok r7 _ _ (by omega)
 intro x7 r8 c7
 have b8 := NID_ReadStepFrame.remaining r7 r8 2 x7 (by exact b7) c7
 apply NID_WithKTransport.source unwrap unwrap_ok r8 _ _ (by omega)
 intro x8 r9 c8
 have b9 := NID_ReadStepFrame.remaining r8 r9 1 x8 (by exact b8) c8
 apply NID_WithKTransport.source unwrap unwrap_ok r9 _ _ (by omega)
 intro x9 r10 c9
 rfl

theorem source (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize)
 (bound : start.val+160≤bytes.val.length) :
 Port5Q2_ReaderSemantic.semantic (T2Nat_ScalarJoin.readK unwrap) bytes start=
 CheckpointBytes4Ops.readSemanticAlpha bytes start := by
 rw [Port5Q2_ReaderSemantic.normalization]
 exact sequence unwrap unwrap_ok bytes start bound
#print axioms sequence
#print axioms source
end NID_SemanticTransport
