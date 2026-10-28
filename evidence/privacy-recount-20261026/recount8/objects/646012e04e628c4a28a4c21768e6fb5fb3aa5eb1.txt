import R1Z.PV_RunJoin_UnifiedRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PureSourceLift
open Aeneas Aeneas.Std Result
open ProverRwRetryModel ProverCommitSemanticTransport26
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N C : Type}
abbrev State (N C : Type) := PV_RunJoin_UnifiedRetry.State N Store C

/-- Pure extracted-body inputs. The external dictionary remains explicit;
this record is NOT a native dictionary or a filesystem/oracle effect handler. -/
structure Inputs (N C : Type) where
  ops : State N C → ProverRwFull.ExternalFuns
  pub : State N C → Pub
  compiled : State N C → Compiled
  hash : State N C → Hash

def sourceBody (d : Inputs N C) : PV_RunJoin_UnifiedRetry.SourceBody (State N C) :=
  ⟨d.ops,d.pub,d.compiled,d.hash,fun s => s.ledger⟩

def native (d : Inputs N C) (s : State N C) (secret : Secret) :=
  letI : ProverRwFull.ExternalFuns := d.ops s
  ProverRwFull.prover.prove_masked_attempt (d.pub s) (d.compiled s) .S2 (d.hash s) secret s.ledger

def body (d : Inputs N C) : PV_RunJoin_UnifiedRetry.Body (State N C) := fun secret s =>
  mapR (fun out => (out.1,{s with ledger := out.2})) (native d s secret)

/-- The body/source equation is discharged for the pure lift, at the actual
full emitted body. No native-world effect equality follows from this lift. -/
theorem source_law (d : Inputs N C) :
    PV_RunJoin_UnifiedRetry.BodySourceLaw (sourceBody d) (body d) := by
  intro s secret
  change mapR (fun out => (out.1,out.2.ledger))
    (mapR (fun out => (out.1,{s with ledger := out.2})) (native d s secret)) = native d s secret
  cases native d s secret with
  | fail e => rfl
  | div => rfl
  | ok out => cases out; rfl

theorem provider_frame (d : Inputs N C) (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof ProverRwFull.verifier.Error)
    (run : body d secret s = .ok (status,next)) : next.provider = s.provider := by
  unfold body at run
  cases computation : native d s secret with
  | fail e => simp only [computation,mapR,bind_tc_fail] at run; cases run
  | div => simp only [computation,mapR,bind_tc_div] at run; cases run
  | ok out =>
    simp only [computation,mapR,bind_tc_ok] at run
    have same := Result.ok.inj run
    exact congrArg (fun pair => pair.2.provider) same.symm

theorem client_frame (d : Inputs N C) (secret : Secret) (s next : State N C)
    (status : core.result.Result Proof ProverRwFull.verifier.Error)
    (run : body d secret s = .ok (status,next)) : next.client = s.client := by
  unfold body at run
  cases computation : native d s secret with
  | fail e => simp only [computation,mapR,bind_tc_fail] at run; cases run
  | div => simp only [computation,mapR,bind_tc_div] at run; cases run
  | ok out =>
    simp only [computation,mapR,bind_tc_ok] at run
    have same := Result.ok.inj run
    exact congrArg (fun pair => pair.2.client) same.symm

#print axioms source_law
#print axioms provider_frame
#print axioms client_frame
end R1Z.PV_RunJoin_PureSourceLift
