import R1PublicInitParse
import R1ParsedTargetsCollision

/-! The parsed initial C1 target as a singleton finite family. -/
set_option autoImplicit false
namespace AspisR1.MerkleC1Target

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps

def pred {L : Nat} (pubBytes : Bytes) (_j : Fin 1) (a : Addr L) : Option State :=
  PublicInitParse.parse pubBytes a

theorem pred_init {L : Nat} (pubBytes : Bytes)
    (hpub : pubBytes.length < 2^32) (hL : 75 + pubBytes.length ≤ L)
    (root : State) :
    pred pubBytes 0 (PublicInitFrame.addr pubBytes hL root) = some root := by
  exact PublicInitParse.parse_addr pubBytes hpub hL root

theorem mass {L : Nat} {X Pf : Type}
    (pubBytes : Bytes) (Qtot : Nat)
    (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (hitsBad (ParsedTargetsCollision.bad (pred pubBytes) Qtot)
        emptyTable (eval H (FS2.experiment P V x)).1)) ≤
      (Qtot : ℚ)^2 / (256^32 : ℚ) := by
  have h := ParsedTargetsCollision.mass (pred pubBytes) Qtot P V x hQ
  simpa [pred, ParsedTargetsCollision.bad] using h

#print axioms pred_init
#print axioms mass

end AspisR1.MerkleC1Target
