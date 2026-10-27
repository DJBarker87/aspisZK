import BEl_ReferenceSource
import BEl_PartialRecorder
import BEl_WeakObservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_NativeBatchCut
open Aeneas Aeneas.Std Result SdkC_Source

/-- Exact operand projection read by the reached safe Rust batch body. Original
Prepared and runtime witnesses are retained by the reached-cut consumer, not
replaced by independently chosen parsed/model arrays. -/
structure Input where
  proof : Slice U8
  queries : Array U32 22#usize
  roots : Array Digest 2#usize
  folded : Digest

def ordinal (slot : Fin 2) : Usize := if slot.val=0 then 0#usize else 1#usize

/-- Direct model of the owned safe Rust reference's physical call observation,
with a pending entry before backend invocation. See BEl_CORRESPONDENCE.md and
BEl_STAGE2.md for the precise external P6 source-certificate boundary. -/
def native {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest)
    (input : Input) (slot : Fin 2) (state : S) (before : Log) :=
  BEl_PartialRecorder.observation (BEl_PartialRecorder.run call
    (BEl_ReferenceSource.code hashv input.proof input.queries input.roots input.folded (ordinal slot))
    state (BEl_Recorder.completed before))

def source {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest)
    (input : Input) (slot : Fin 2) (state : S) (before : Log) :=
  BEf_Carrier.run call (SdkC_BatchSource.code (dictionary hashv) ()
    input.proof input.queries input.roots input.folded (ordinal slot)) state before

/-- Uniform BothSlots instance for the direct reference observation. All safe
operand values are covered, so actual reached-cut admission implies this domain
without a success/log/desired-conclusion hypothesis. Its physical source bridge
is the separately audited P6 certificate, not an additional Lean axiom. -/
theorem observation {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest) :
    BEh_Scope.BothSlots (fun (_ : Input) (_ : Fin 2) (_ : S) => True)
      (native call hashv) (source call hashv) := by
  intro input slot state before _
  unfold native source
  rw [BEl_PartialRecorder.correspondence]
  apply BEl_WeakObservation.law
  exact BEl_ReferenceSource.observation call hashv input.proof input.queries input.roots input.folded
    (ordinal slot) state before

theorem logs {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest)
    (input : Input) (slot : Fin 2) (state : S) (before : Log) :
    (native call hashv input slot state before).2.2 = (source call hashv input slot state before).2.2 :=
  BEh_Scope.logs _ _ (observation call hashv input slot state before trivial)

#print axioms observation
#print axioms logs
end AspisR1.BEl_NativeBatchCut
end
