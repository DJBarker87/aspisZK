import R1FixedOffsetTarget
import R1ParsedTargetsCollision

/-! Two mechanical root target readers for commitment trace rows. -/
set_option autoImplicit false
namespace AspisR1.CommitmentRootTargets

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling

def pred {L : Nat} (j : Fin 2) (a : Addr L) : Option State :=
  if j.val = 0 then TrailingStateFrame.tailState a else FixedOffsetTarget.parse 38 a

theorem pred_tail {L : Nat} (pre : Bytes) (root : State)
    (hlen : (TrailingStateFrame.frame pre root).length ≤ L) :
    pred 0 (TrailingStateFrame.frameAddr pre root hlen) = some root := by
  simpa [pred] using TrailingStateFrame.tailState_frameAddr pre root hlen

theorem pred_middle {L : Nat} (pre : Bytes) (root : State) (tail : Bytes)
    (hpre : pre.length = 38)
    (hlen : (pre ++ bytes root ++ tail).length ≤ L) :
    pred 1 (Addr.ofBytes (pre ++ bytes root ++ tail) hlen) = some root := by
  simpa [pred] using FixedOffsetTarget.parse_ofBytes 38 pre root tail hpre hlen

theorem mass {L : Nat} {X Pf : Type} (Qtot : Nat)
    (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
        (eval H (FS2.experiment P V x)).1)) ≤
      2 * (Qtot : ℚ)^2 / (256^32 : ℚ) := by
  have h := ParsedTargetsCollision.mass pred Qtot P V x hQ
  simpa [pred, mul_assoc] using h

#print axioms pred_tail
#print axioms pred_middle
#print axioms mass

end AspisR1.CommitmentRootTargets
