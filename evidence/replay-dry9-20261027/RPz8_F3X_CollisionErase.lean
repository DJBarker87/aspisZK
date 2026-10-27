import RPz8_F3X_Trace
import RPz7_F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_CollisionErase
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- A repeated already-read preparation pass does not change the collision
event, even when the following replay is adaptive. This is erasure of cache
hits at the end of the complete source, not reordering first reads. -/
theorem same (H : Bytes → State) (source preparation : List (Bytes × State))
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (sourceConsistent : ∀ a∈source,a.2=H a.1)
    (preparationConsistent : ∀ a∈preparation,a.2=H a.1)
    (included : ∀ a,Read preparation a → Read source a) :
    AuS1_Finish.Collision H (source++preparation) p q ↔ AuS1_Finish.Collision H source p q := by
  unfold AuS1_Finish.Collision
  rw [OracleProgramRecording.firstReads_append_reused source preparation included]
  exact F3X_Trace.erase_reused _ H source preparation _ sourceConsistent preparationConsistent included

#print axioms same
end AspisR1.F3X_CollisionErase
end
