import R1Z.ProverCommitFront46
import R1Z.ProverCommitPublication45
import R1Z.ProverCommitProgramLog46
/-! Final publication preserves proof bytes, ordered tables, retained read
counts and exact error precedence. No proof or table is returned on error. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFinalize46
open ProverCommitTrustedStd24 ProverCommitProgramOne46
open ProverCommitPublish43 (Bytes Error)
attribute [local instance] Classical.propDecidable
variable {Key Table Thread Slot Output : Type}
variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
structure Published (Table : Type) where
  proof : Bytes
  table : Table
  attempts : Nat
  transcriptReads : Nat
  commitmentReads : Nat

def decode (map : MapAPI Key Bytes32 Table cmp) (out : Published Table) :=
  Published.mk out.proof (map.decode out.table) out.attempts out.transcriptReads out.commitmentReads

def finish (map : MapAPI Key Bytes32 Table cmp) (proof : Except Error Bytes)
    (replay : Except Error Bool) (state : State Table) (transcript : Table)
    (k reads : Nat) : Except Error (Published Table) :=
  proof.bind (fun proof => replay.bind (fun agrees =>
  if !agrees then .error .transcript else
    if state.collision then .error .merkle else
      match ProverCommitPublication45.publication map state.table transcript with
      | none => .error .transcript
      | some final => .ok ⟨proof,final.1,k+1,final.2,reads⟩))

variable [DecidableEq Thread]
variable (map : MapAPI Key Bytes32 Table cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (std : TrustedStd map tls thread schedule)
include std

theorem finish_decode (proof : Except Error Bytes) (replay : Except Error Bool)
    (state : State Table) (transcript : Table) (k reads : Nat) :
    (finish map proof replay state transcript k reads).map (decode map) =
      finish modelMap proof replay (ProverCommitProgramOne46.decode map state)
        (map.decode transcript) k reads := by
  cases proof with
  | error e => rfl
  | ok proof =>
    cases replay with
    | error e => rfl
    | ok agrees =>
      cases agrees with
      | false => rfl
      | true =>
        cases hc : state.collision with
        | true => simp only [finish,hc,ProverCommitProgramOne46.decode,Except.bind,Bool.not_true,
            Bool.false_eq_true,if_false,if_true,Except.map]
        | false =>
          have h := ProverCommitPublication45.publication_decode tls thread schedule map std state.table transcript
          cases hp : ProverCommitPublication45.publication map state.table transcript with
          | none =>
            simp only [hp,Option.map_none] at h
            simp only [finish,hc,ProverCommitProgramOne46.decode,Except.bind,Bool.not_true,
              Bool.false_eq_true,if_false,hp,←h,Except.map]
          | some result =>
            simp only [hp,Option.map_some] at h
            simp only [finish,hc,ProverCommitProgramOne46.decode,Except.bind,Bool.not_true,
              Bool.false_eq_true,if_false,hp,←h,Except.map,decode]

/-- The complete ProgramOne sequence feeds the actual final flag and map to
the finalizer; equal returned digests alone are not used. -/
theorem programming_publication (address : Parts → Key)
    (requests : List ProverCommitProgramLog46.Request) (state : State Table)
    (proof : Except Error Bytes) (replay : Except Error Bool) (transcript : Table)
    (k reads : Nat) :
    (do let result ← ProverCommitProgramLog46.run map address requests state
        Aeneas.Std.Result.ok ((finish map proof replay result.2 transcript k reads).map (decode map))) =
      Aeneas.Std.Result.ok (finish modelMap proof replay
        (ProverCommitProgramLog46.expected modelMap address requests
          (ProverCommitProgramOne46.decode map state)).2 (map.decode transcript) k reads) := by
  rw [ProverCommitProgramLog46.run_exact]
  simp only [Aeneas.Std.bind_tc_ok,finish_decode map tls thread schedule std]
  have h := ProverCommitProgramLog46.expected_decode map tls thread schedule std address requests state
  have hs := congrArg Prod.snd h
  change ProverCommitProgramOne46.decode map (ProverCommitProgramLog46.expected map address requests state).2 = _ at hs
  rw [hs]

#print axioms finish_decode
#print axioms programming_publication
end R1Z.ProverCommitFinalize46
