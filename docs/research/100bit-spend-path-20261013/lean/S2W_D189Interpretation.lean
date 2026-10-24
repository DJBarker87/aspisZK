import S2W_AccountObservations
import S2W_Trace

/-! D189: instantiate the existing SDK interpretation, rather than requesting
an additional whole-wrapper equivalence hypothesis. The account observations
read native SDK cells; metadata is the runtime ambient account record.
The owned evaluator cannot receive or return an account-state capability. -/
set_option autoImplicit false
namespace AspisR1.S2W_D189Interpretation
open S2Trust S2W_EntryWriteHistory S2W_AccountObservations
open Aeneas Aeneas.Std Result S2W_Trace

/-- Native data observation through the actual typed SDK library carrier.
The ambient parameter is the runtime metadata interpretation, not an inferred
OwnedAccount projection (which omits lamports and rentEpoch). -/
def nativeObserve {W F : Type} (L : Library W F)
    (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat)
    (w : W) (ambient : F) (a : Nat) : S2LeadInterface.Account :=
  if a < n then
    {metadata ambient a with data := (payloadBytes encode
      (L.cellPayload w (L.accountData w a))
      (L.cellPayload w (L.accountData w a)).descriptor.length)}
  else metadata ambient a

/-- The native AccountInfo/heap association is obtained from exactly the
approved account_data_cell and cell_payload fields. It is not a caller
postcondition, source equality, or new native-binding assumption. -/
theorem native_observation {W F : Type} (L : Library W F)
    (sdk : S2TrustedSdkBorrow L)
    (encode : UInt8 → AspisV8R19.DuplexFrames.Byte)
    (metadata : F → Nat → S2LeadInterface.Account) (n : Nat)
    (w : W) (s : Heap F) (related : L.related w s) (valid : Valid s) :
    nativeObserve L encode metadata n w s.ambient = observe encode metadata n s := by
  funext a
  have cell := (sdk.account_data_cell w s related valid a a).1
  have payload := sdk.cell_payload w s related valid (s.accounts a).1
  simp only [nativeObserve,observe,cell,payload]

/-- The native counter/guard ledger is the SAME heap's ledger. -/
theorem native_counter {W F : Type} (L : Library W F)
    (sdk : S2TrustedSdkBorrow L) (w : W) (s : Heap F)
    (related : L.related w s) (valid : Valid s) (c : Nat) :
    L.cellCounter w c = s.counter c ∧ ∀ t, L.liveGuard w t = lookup s t :=
  sdk.cell_counter w s related valid c

/-- State extension of the extracted typed evaluator. Its calls have exactly
the extracted owned signatures; no AccountInfo or Heap argument is passed to
invoke. Account state is threaded separately from owned values and call log. -/
def runOwned {F A : Type} (ops : AdapterRw.Ops) :
    Code A → Log → Heap F → Result (A × Log × Heap F)
  | .done a, log, s => ok (a,log,s)
  | .step r k, log, s => thenResult r (fun b => runOwned ops (k b) log s)
  | .call call k, log, s => thenResult (invoke ops call) (fun b =>
      runOwned ops (k b) (log ++ [.returned call b]) s)

/-- Signature-derived frame, by induction over EVERY extracted call and
continuation, including errors/divergence. No child-frame premise is used. -/
theorem owned_account_frame {F A : Type} (ops : AdapterRw.Ops)
    (code : Code A) (log : Log) (s : Heap F) :
    runOwned ops code log s =
      thenResult (S2W_Trace.run ops code log) (fun answer => ok (answer.1,answer.2,s)) := by
  induction code generalizing log with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok b => exact ih b log
    | fail e => rfl
    | div => rfl
  | call call k ih =>
    cases invoked : invoke ops call with
    | ok b => simpa only [runOwned,S2W_Trace.run,invoked,thenResult] using ih b (log ++ [.returned call b])
    | fail e => simp only [runOwned,S2W_Trace.run,invoked,thenResult]
    | div => simp only [runOwned,S2W_Trace.run,invoked,thenResult]

/-- Specialization to the actual accepted owned execution, with the account
heap unchanged and the exact typed log retained. -/
theorem accepted_owned_frame {F A : Type} (ops : AdapterRw.Ops)
    (code : Code A) (before after : Log) (value : A) (s : Heap F)
    (accepted : S2W_Trace.run ops code before = ok (value,after)) :
    runOwned ops code before s = ok (value,after,s) := by
  rw [owned_account_frame,accepted]; rfl

#print axioms native_observation
#print axioms native_counter
#print axioms owned_account_frame
#print axioms accepted_owned_frame
end AspisR1.S2W_D189Interpretation
