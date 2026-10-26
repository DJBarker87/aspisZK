import ARS_QueryTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_PartialProgram
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.SqueezeOracleBridge

/-- Syscall status is retained, including its failure at the reached address.
The oracle answer at a failed call is a ghost charge and is never returned
as a successful native digest or used to choose a continuation. -/
def program {A : Type} (hashv : Parts → Result Digest) :
    Code A → Log → Program Bytes State (Result A × Log)
  | .done a, before => .done (ok a,before)
  | .step r k, before => match r with
    | .ok a => program hashv (k a) before
    | .fail e => .done (.fail e,before)
    | .div => .done (.div,before)
  | .read parts k, before => .ask (flatten parts) fun value =>
    match hashv parts with
    | .ok _ => program hashv (k (encodeState value))
        (before ++ [⟨parts,ok (encodeState value)⟩])
    | .fail e => .done (.fail e,before ++ [⟨parts,.fail e⟩])
    | .div => .done (.div,before ++ [⟨parts,.div⟩])

/-- Query-restricted agreement follows the ACTUAL partial execution, not the
ideal successful suffix. Failed calls need no invented successful value. -/
def Compatible {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State) : Code A → Prop
  | .done _ => True
  | .step r k => match r with
    | .ok a => Compatible hashv H (k a)
    | .fail _ => True
    | .div => True
  | .read parts k => match hashv parts with
    | .ok digest => decodeState digest = H (flatten parts) ∧ Compatible hashv H (k digest)
    | .fail _ => True
    | .div => True

/-- Attempted addresses include the rejected call, with duplicates intact.
The answer component is ghost bookkeeping, separate from the native Log. -/
def attempted (H : Bytes → State) (log : Log) : List (Bytes × State) :=
  log.map (fun q => (flatten q.parts,H (flatten q.parts)))

theorem exact {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (before : Log) (compatible : Compatible hashv H code) :
    (eval H (program hashv code before)).2 = run hashv code before ∧
    attempted H before ++ (eval H (program hashv code before)).1 =
      attempted H (run hashv code before).2 := by
  induction code generalizing before with
  | done a => exact ⟨rfl,List.append_nil _⟩
  | step r k ih =>
    cases r with
    | ok a => exact ih a before compatible
    | fail e => exact ⟨rfl,List.append_nil _⟩
    | div => exact ⟨rfl,List.append_nil _⟩
  | read parts k ih =>
    cases answer : hashv parts with
    | ok digest =>
      have facts : decodeState digest = H (flatten parts) ∧ Compatible hashv H (k digest) := by
        simpa only [Compatible,answer] using compatible
      have encoded : encodeState (H (flatten parts)) = digest := by
        rw [←facts.1]; exact array_roundtrip digest
      obtain ⟨out,log⟩ := ih digest (before ++ [⟨parts,ok digest⟩]) facts.2
      simp only [program,eval,answer,encoded,run]
      refine ⟨out,?_⟩
      simpa only [attempted,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
        List.singleton_append] using log
    | fail e =>
      simp only [program,eval,answer,run,attempted,List.map_append,List.map_cons,
        List.map_nil,List.append_nil]
      exact ⟨True.intro,rfl⟩
    | div =>
      simp only [program,eval,answer,run,attempted,List.map_append,List.map_cons,
        List.map_nil,List.append_nil]
      exact ⟨True.intro,rfl⟩

#print axioms exact
end AspisR1.ART_PartialProgram
end
