import NNH_MerkleRowsExecute
import NJV_NativeEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleLevelsExecute
open Aeneas Aeneas.Std NJP_RowModel NJP_LoopModel
attribute [local instance] Classical.propDecidable

def run (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
 Nat → Scratch → List (Request × Digest) × Level
 | 0,s => ([],.done s)
 | height+1,s =>
   let row := NNH_MerkleRowsExecute.run H nodes length s.n s 0 0
   match row.2 with
   | .stop after => (row.1,.stop after)
   | .done after =>
     let tail := run H nodes length height after
     (row.1++tail.1,tail.2)

theorem native (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
 (s : Scratch) : NJV_NativeLevels.Invocation H nodes length height s
  (run H nodes length height s).1 (run H nodes length height s).2 := by
 induction height generalizing s with
 | zero => exact .final s
 | succ height ih =>
   have row := NNH_MerkleRowsExecute.native H nodes length s.n s 0 0 (by omega)
   cases answer : (NNH_MerkleRowsExecute.run H nodes length s.n s 0 0).2 with
   | stop after =>
     simp only [answer] at row
     simp only [run,answer]
     exact .stop height s after _ row
   | done after =>
     simp only [answer] at row
     simp only [run,answer]
     exact .next height s after _ _ _ row (ih after)

/-- Concrete terminal invocation at the original18 heights, including early
rejection, every first-error prefix and both complete scratch buffers. -/
def entry (H : Request → Digest) (root : NJP_DigestCarrier.RefDigest)
 (physical : Slice U8) (s : MultiproofConeRef.reference.Scratch) :
 List (Request × Digest) × (Bool × Scratch) :=
 if NJV_Entry.Guard physical s then
  let result := run H (fun n => physical.val[n]!) physical.val.length 18
   {NJP_ScratchCarrier.raw s with cursor:=0}
  (result.1,finish (NJP_DigestCarrier.decode root) physical.val.length result.2)
 else ([],(false,NJP_ScratchCarrier.raw s))

theorem entry_native (H : Request → Digest) (root : NJP_DigestCarrier.RefDigest)
 (physical : Slice U8) (s : MultiproofConeRef.reference.Scratch) :
 NJV_NativeEntry.Invocation H root physical s (entry H root physical s).1 (entry H root physical s).2 := by
 unfold entry
 split
 · rename_i guard
   exact .returned _ _ guard (native H _ _ _ _)
 · rename_i guard
   exact .rejected guard
#print axioms native
#print axioms entry_native
end AspisR1.NNH_MerkleLevelsExecute
