import SdkC_SourceLaws
import MultiproofConePhysicalProgram
import Port4B_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_NativeNode
open Aeneas Aeneas.Std Result
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeRef MultiproofConePhysicalProgram

/-- Reify the physical program without assuming that its digest calls return. -/
def reify {A : Type} : Run A → SdkC_Source.Code A
  | .done r => .step r .done
  | .ask parts next => .read parts (fun d => reify (next d))


def digest {Hash : Type} (D : aspis_core.digest.Digest32 Hash) :
    AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
  {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}

theorem erase_writer {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (left right : Digest) (ni cursor : Usize) (index : U32) (w : Usize) :
    CheckpointBytes5Effect.erase (digest D) hash (reify (writer s left right ni cursor index w)) =
      reference.write_parent D hash s left right ni cursor index w := by
  have rightIdentity {A : Type} (r : Result A) : (do let a ← r; ok a) = r := by
    cases r <;> rfl
  change (do let d ← D.digest hash (MultiproofConePhysicalDigest.parts left right)
             let a ← finish s d ni cursor index w
             ok a) = _
  simp only [rightIdentity]
  unfold reference.write_parent
  change (do let d ← D.digest hash (MultiproofConePhysicalDigest.parts left right)
             finish s d ni cursor index w) = _
  rfl

theorem erase_checked {Hash A B : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (r : Result A) (next : A → Run B) :
    CheckpointBytes5Effect.erase (digest D) hash (reify (checked r next)) =
      (do let a ← r; CheckpointBytes5Effect.erase (digest D) hash (reify (next a))) := by
  cases r <;> rfl

theorem erase_conditional {Hash A : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (p : Prop) [Decidable p] (yes no : Run A) :
    CheckpointBytes5Effect.erase (digest D) hash (reify (if p then yes else no)) =
      if p then CheckpointBytes5Effect.erase (digest D) hash (reify yes)
      else CheckpointBytes5Effect.erase (digest D) hash (reify no) := by split <;> rfl

/-- All-input partial source association for the concrete P6/native node.
The reply consumed by the continuation is exactly the returned hash reply. -/
theorem erase_node {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    CheckpointBytes5Effect.erase (digest D) hash (reify (node s physical i w)) =
      reference.binary_step D hash s physical i w := by
  simp only [node,erase_checked,erase_conditional,erase_writer]
  unfold reference.binary_step
  rfl

/-- Exact native node return and its source-computed log, with no child port. -/
theorem source_node (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (reify (node s physical i w)) before).1 =
      reference.binary_step
        {coremarkerCopyInst := (SdkC_Source.dictionary hashv).coremarkerCopyInst,
          digest := (SdkC_Source.dictionary hashv).digest} () s physical i w := by
  let D : aspis_core.digest.Digest32 Unit :=
    {coremarkerCopyInst := (SdkC_Source.dictionary hashv).coremarkerCopyInst,
      digest := (SdkC_Source.dictionary hashv).digest}
  exact (SdkC_Source.erasure_to (digest D) () hashv (fun _ => rfl) _ before).trans
    (erase_node D () s physical i w)

/-- Actual installed native leaf, not a logical opening selected independently. -/
theorem source_leaf (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (kind : Usize) (opening : Slice U8) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (Port4B_LeafCode.code kind opening) before).1 =
      Port4B_Install.leaves.op6 (SdkC_Source.dictionary hashv) () kind opening := by
  exact SdkC_Source.erasure hashv _ before

#print axioms erase_writer
#print axioms erase_checked
#print axioms erase_conditional
#print axioms erase_node
#print axioms source_node
#print axioms source_leaf
end AspisR1.SdkC_NativeNode
end
