import SdkC_Source
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Carrier
open Aeneas Aeneas.Std Result SdkC_Source

/-- A read may update a carrier even when it fails. The carrier and attempted
call log are outside Result, so no rejected prefix is discarded. -/
def run {S A : Type} (call : Parts → S → Result Digest × S) :
    Code A → S → Log → Result A × S × Log
  | .done a, state, log => (.ok a,state,log)
  | .step r k, state, log => match r with
    | .ok a => run call (k a) state log
    | .fail e => (.fail e,state,log)
    | .div => (.div,state,log)
  | .read parts k, state, log =>
    let (answer,next) := call parts state
    let log' := log ++ [⟨parts,answer⟩]
    match answer with
    | .ok digest => run call (k digest) next log'
    | .fail e => (.fail e,next,log')
    | .div => (.div,next,log')

def project {S A : Type} (answer : Result A × S × Log) : Result A × Log :=
  (answer.1,answer.2.2)

/-- Value/log projection does not require a carrier-frame assumption. In
particular, the premise does not constrain the syscall's state update. -/
theorem source {S A : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (code : Code A) (state : S) (log : Log) :
    project (run call code state log) = SdkC_Source.run hashv code log := by
  induction code generalizing state log with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a state log
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    unfold run
    split
    next answer next h =>
      have same : answer = hashv parts := by
        simpa only [h] using binding parts state
      subst answer
      cases result : hashv parts with
      | ok digest =>
        simpa only [SdkC_Source.run,result] using
          ih digest next (log ++ [⟨parts,.ok digest⟩])
      | fail e => rfl
      | div => rfl

/-- Framing is a separate condition; it must be proved for a native instance. -/
theorem frame {S A : Type} (call : Parts → S → Result Digest × S)
    (preserves : ∀ parts state, (call parts state).2 = state)
    (code : Code A) (state : S) (log : Log) :
    (run call code state log).2.1 = state := by
  induction code generalizing state log with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a state log
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    unfold run
    split
    next answer next h =>
      have same : next = state := by simpa only [h] using preserves parts state
      subst next
      cases answer with
      | ok digest => exact ih digest state _
      | fail e => rfl
      | div => rfl

#print axioms source
#print axioms frame
end AspisR1.BEf_Carrier
end
