import Port10AUTH_Trace

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Total
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- Proof-only total oracle. Never installed in the source experiment. -/
def dictionary {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (H : Bytes → State) : AspisR1Stage2.aspis_core.digest.Digest32 X :=
  {D with digest := fun _ parts => ok (encodeState (H (flatten parts)))}

/-- Replacing only failed/divergent primitive outcomes has no effect on ANY
part of an actual successful Code trace. Repeated calls are retained. -/
theorem replace {A X : Type} (D E : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (p : Code A) (out : A)
    (agree : ∀ parts digest, D.digest hash parts=ok digest → E.digest hash parts=ok digest)
    (accepted : erase D hash p=ok out) :
    Port9OR_Code.trace E hash p=Port9OR_Code.trace D hash p := by
  induction p with
  | done a => rfl
  | step r k ih => cases r with
    | fail e => cases accepted
    | div => cases accepted
    | ok a => exact ih a accepted
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [erase,call,bind_tc_fail] at accepted;cases accepted
    | div => simp only [erase,call,bind_tc_div] at accepted;cases accepted
    | ok d =>
      simp only [erase,call,bind_tc_ok] at accepted
      simp only [Port9OR_Code.trace,call,agree parts d call,ih d accepted]

/-- Actual success and the per-successful-read Oracle fact suffice; totality
on any unexecuted input is not a source premise. -/
theorem accepted {A X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (H : Bytes → State) (p : Code A) (out : A)
    (oracle : CheckpointBytes5Inputs.Oracle D hash H) (success : erase D hash p=ok out) :
    Port9OR_Code.trace (dictionary D H) hash p=Port9OR_Code.trace D hash p := by
  apply replace D (dictionary D H) hash p out _ success
  intro parts d call
  have same : decodeState d=H (flatten parts) := oracle parts d call
  have digest : encodeState (H (flatten parts))=d := (congrArg encodeState same).symm.trans (array_roundtrip d)
  simp only [dictionary,digest]

#print axioms replace
#print axioms accepted
end AspisR1.Port10AUTH_Total
end
