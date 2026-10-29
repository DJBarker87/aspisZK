import R1Z.PV_RunJoin_QueryLinkObstruction56
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryNativeObstruction56
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54

def buffer (n : Nat) (bound : n≤Usize.max) : alloc.vec.Vec U8 :=
  ⟨List.replicate n 0#u8,by simpa only [List.length_replicate] using bound⟩

theorem buffer_length (n : Nat) (bound : n≤Usize.max) : (buffer n bound).length=n := by
  change (List.replicate n 0#u8).length=n
  exact List.length_replicate

/-- These fields are never read: the first index rejects before opening. -/
def unused (p : prover.Publication) : host_commitment.Commitment :=
  ⟨.C1,⟨[],by simp⟩,⟨[],by simp⟩,p.tree,none⟩

theorem complete {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base)) (i : I)
    (p : prover.Publication)
    (hf : @Fields (types base) (selected base heap box ops) (runs i) p)
    (bound : (@Run.plan (types base) (runs i)).offOpenings≤Usize.max) :
    ¬@PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) I runs := by
  exact @PV_RunJoin_QueryLinkObstruction56.impossible (types base) (selected base heap box ops)
    I runs i p (unused p) (unused p) (buffer _ bound) hf (buffer_length _ bound)
    (PV_RunJoin_QueryIndexInstalled56.rejected base heap box ops)

#print axioms buffer
#print axioms buffer_length
#print axioms unused
#print axioms complete
end R1Z.PV_RunJoin_QueryNativeObstruction56
