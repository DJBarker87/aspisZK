import R1CanonicalMerkleCollision

/-! Lift a byte-level Merkle collision into an arbitrary consistent oracle
trace when the prior and opening reads both occur in that trace. -/
set_option autoImplicit false
namespace AspisR1.CanonicalReadCollision

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf CanonicalByteHash

variable {L : Nat}

theorem hits_collision {M Cv : Type} (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hpreRead : ∀ a, Read pre a → Read tr a)
    {slots : List (Fin 8)} (path : Path slots) (leaf : Bytes)
    (hleaf : leaf.length ≤ L) (hnode : 257 ≤ L)
    (hpostRead : ∀ a, Read (eval H (CanonicalMerkleProgram.program path leaf)).1 a →
      Read tr a)
    (hc : CrossTraceCollision (hashBytes H) ((CanonicalOracleLog.byteLog pre).map Prod.fst)
      (fullTrace (hashBytes H) path leaf)) :
    hitsBad (badColl p Qtot) emptyTable tr := by
  classical
  by_contra hfree
  obtain ⟨a, b, ha, hb, hne, hhash⟩ :=
    CanonicalMerkleCollision.read_witness H pre path leaf hleaf hnode hc
  exact noColl_injective p Qtot H tr hcons hQ hfree a b
    (hpreRead a ha) (hpostRead b hb) hne hhash

#print axioms hits_collision

end AspisR1.CanonicalReadCollision
