import NKV_ParentSource
import NKV_ConcreteChildren
set_option autoImplicit false
noncomputable section
namespace NKV_OuterSource
open Aeneas Aeneas.Std Result AspisR1Stage2
open NKV_StepErasure NKV_ParentSource

theorem bind_observed {A : Type} (m : Result A) (f g : A → Result Reply)
 (same : ∀ x,observe (f x)=observe (g x)) :
 observe (m >>= f)=observe (m >>= g) := by
 cases m with
 | fail e => rfl
 | div => rfl
 | ok x => exact same x

theorem source (base : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
 (batch : Usize) (bound : batch.val<2) :
 observe (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle
   (AspisR1.Port3_BatchStd.install base) D proof p folded batch hash)=
 observe (NKV_FRef.verifier.candidate.batch_merkle
   (AspisR1.Port3_BatchStd.install base) D proof p folded batch hash) := by
 unfold AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle
   NKV_FRef.verifier.candidate.batch_merkle
 apply bind_observed
 intro root0
 apply bind_observed
 intro root1
 exact NKV_ParentSource.values base D hash proof p.queries _ batch bound

theorem values_concrete (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (proof : Slice U8) (queries : Array U32 22#usize)
 (roots : Array (Array U8 32#usize) 3#usize) (batch : Usize) (bound : batch.val<2) :
 observe (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
   (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof queries roots batch ())=
 observe (NKV_FRef.verifier.candidate.batch_merkle_values
   (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof queries roots batch ()) := by
 simpa only [NKV_ConcreteChildren.installed] using
   NKV_ParentSource.values (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) ()
     proof queries roots batch bound

theorem concrete (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (proof : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
 (batch : Usize) (bound : batch.val<2) :
 observe (AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_merkle
   (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof p folded batch ())=
 observe (NKV_FRef.verifier.candidate.batch_merkle
   (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof p folded batch ()) := by
 simpa only [NKV_ConcreteChildren.installed] using
   source (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) () proof p folded batch bound

set_option pp.proofs false
#print concrete
#print values_concrete
#print axioms bind_observed
#print axioms source
#print axioms values_concrete
#print axioms concrete
end NKV_OuterSource
end
