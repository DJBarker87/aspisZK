import Port9OR_Code
import Port4B_VerifyInstall

/-! Physical P6 parent/node reification at concrete source types. Every
successful parent reply is written to scratch before the next node. Errors are
not excluded by a total-oracle premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_P6Node
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConePhysicalDigest MultiproofConePhysicalProgram

/-- Actual source hash components and post-hash checked mutations. -/
def parent (s : reference.Scratch) (left right : CheckpointBytes5Effect.Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) : Code reference.Row :=
  .read (parts left right) fun digest =>
    liftResult (finish s digest ni cursor index w)

def node (s : reference.Scratch) (physical : Slice U8) (i w : Usize) : Code reference.Row :=
  .step (Array.index_usize s.idx i) fun index =>
  .step (Array.index_usize s.val i) fun value =>
  .step (i+1#usize) fun ni =>
  let supplied : Code reference.Row :=
    .step (Slice.len physical-s.«at») fun remaining =>
    if remaining<32#usize then .done (.Stop s) else
    .step (s.«at»+32#usize) fun cursor =>
    .step (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      physical {start:=s.«at»,«end»:=cursor}) fun chunk =>
    .step (reference.read32 chunk) fun sibling =>
    if index &&& 1#u32=0#u32 then parent s value sibling ni cursor index w
    else parent s sibling value ni cursor index w
  if ni<s.n then
    .step (Array.index_usize s.idx ni) fun nextIndex =>
    if nextIndex=index^^^1#u32 then
      .step (Array.index_usize s.val ni) fun right =>
      .step (i+2#usize) fun next => parent s value right next s.«at» index w
    else supplied
  else supplied

def digest {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) :
    aspis_core.digest.Digest32 Hash := ⟨D.coremarkerCopyInst,D.digest⟩

/-- Full native Result, including hash failure/divergence and checked writes. -/
theorem parent_source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) (left right : CheckpointBytes5Effect.Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) :
    erase D hash (parent s left right ni cursor index w)=
      reference.write_parent (digest D) hash s left right ni cursor index w := by
  simp only [parent,erase,erase_lift]
  unfold reference.write_parent
  rfl

theorem node_source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    erase D hash (node s physical i w)=reference.binary_step (digest D) hash s physical i w := by
  simp only [node,erase,erase_ite,parent_source]
  unfold reference.binary_step
  rfl

/-- All-H concrete P6 node source/effect instance under the fixed Program. -/
theorem node_value {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) (physical : Slice U8) (i w : Usize)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) :
    (AspisV8R19.MemoizedProgramLaw.eval H (Port9OR_Code.program D hash (node s physical i w))).2=
      reference.binary_step (digest (Port9OR_Code.native D H)) hash s physical i w := by
  rw [Port9OR_Code.value,node_source]

#print axioms parent_source
#print axioms node_source
#print axioms node_value
end AspisR1.Port9OR_P6Node
end
