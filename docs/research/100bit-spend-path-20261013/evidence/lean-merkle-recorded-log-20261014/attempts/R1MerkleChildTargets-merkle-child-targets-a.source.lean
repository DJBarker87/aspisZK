import R1MerkleNodeCodec
import R1ParsedTargetsCollision

/-! Eight fixed child-position parsers for literal node-input targets. This
adapter concerns node CHILD targets only; it does not infer root parsers or
claim full Merkle binding. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.MerkleChildTargets

open FS2.Duplex
open AspisR1.Merkle32Path
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {L : Nat}

def pred (slot : Fin 8) (a : Addr L) : Option State :=
  (MerkleNodeCodec.parse a.toBytes).map fun children => children slot

theorem pred_ofBytes (children : Children) (slot : Fin 8) (hlen : 257 ≤ L) :
    pred slot (Addr.ofBytes (nodeInput children) hlen) = some (children slot) := by
  simp [pred, Addr.toBytes_ofBytes, MerkleNodeCodec.parse_nodeInput]

theorem mass {X Pf : Type} (Qtot : Nat)
    (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
        (eval H (FS2.experiment P V x)).1)) ≤
      (8 : ℚ) * (Qtot : ℚ)^2 / (256^32 : ℚ) := by
  simpa using ParsedTargetsCollision.mass (B := 8) pred Qtot P V x hQ

#print axioms pred_ofBytes
#print axioms mass

end AspisR1.MerkleChildTargets
end
