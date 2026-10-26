import R1Z.ProverCommitLedgerCoupling39
import R1Z.ProverCommitPrivateMemo40

/-! Public, adversary-chosen nonce route. The owned model uses two raw seed
blocks, with the native zero guard and sixteen-candidate limit. This is not
an extraction certificate for generate_for_mask_nonce. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPublicNonce40
open R0Z.FsStatement ProverCommitLedger36
attribute [local instance] Classical.propDecidable
abbrev Raw := Fin 2 → OracleAnswer
abbrev Private := {raw : Raw // ∀ i, raw i ≠ 0}
abbrev EntropyError := ProverCommitEntropy18.Error ProverCommitEnvironment35.IOError
abbrev Error := ProverCommitEnvironment35.Error

def decode (raw : Raw) : Option Private :=
  if good : ∀ i, raw i ≠ 0 then some ⟨raw,good⟩ else none

def next (schedule : Schedule) (tape : Nat → Raw) (s : State) :
    Except ProverCommitEnvironment35.IOError Raw × State :=
  let (result,after) := ask schedule .rng s
  match result with
  | .error e => (.error e,after)
  | .ok _ => (.ok (tape s.cursor),{after with cursor := s.cursor+1})

def run (schedule : Schedule) (tape : Nat → Raw) :
    Nat → State → Except EntropyError Private × State
  | 0, s => (.error .repeatedZero,s)
  | fuel+1, s =>
    let (result,after) := next schedule tape s
    match result with
    | .error e => (.error (.os e),after)
    | .ok raw =>
      match decode raw with
      | none => run schedule tape fuel after
      | some secret => (.ok secret,after)

/-- The nonce is checked before any RNG call; it is never sampled. -/
def generate (nonce : Path) (schedule : Schedule) (tape : Nat → Raw) (s : State) :
    Except EntropyError Private × State :=
  if nonce = 0 then (.error .repeatedZero,s) else run schedule tape 16 s

/-- E1 at the actual 64-byte successful OS-return carrier. This is the same
named environmental trust item, specialised to the actual API draw size. -/
def E1 {C : Type} (law : C → Raw → ℚ) : Prop :=
  ∀ context raw, law context raw = 1 / (Fintype.card Raw : ℚ)

def prepare (address : Path → Path) (nonce : Path) (schedule : Schedule)
    (tape : Nat → Raw) (unix : Bool) (s : State) : Except Error Private × State :=
  let (result,after) := generate nonce schedule tape s
  match result with
  | .error e => (.error (.entropy e),after)
  | .ok secret =>
    let (reserved,final) := reserve schedule unix (address nonce) after
    (reserved.map (fun _ => secret) |>.mapError ProverCommitEnvironment35.Error.reservation,final)

def withPrepared {W P : Type} (address : Path → Path) (nonce : Path)
    (schedule : Schedule) (tape : Nat → Raw) (unix : Bool) (s : State) (w : W)
    (continuation : W → Private → State → Except Error P × State) :
    Except Error P × State :=
  match prepare address nonce schedule tape unix s with
  | (.error e,after) => (.error e,after)
  | (.ok secret,after) => continuation w secret after

theorem zero_guard (schedule : Schedule) (tape : Nat → Raw) (s : State) :
    generate 0 schedule tape s = (.error .repeatedZero,s) := by simp [generate]

theorem decode_success (secret : Private) : decode secret.val = some secret := by
  simp only [decode,dif_pos secret.property]

theorem run_os_error (schedule : Schedule) (tape : Nat → Raw)
    (s after : State) (e : ProverCommitEnvironment35.IOError) (fuel : Nat)
    (failed : next schedule tape s = (.error e,after)) :
    run schedule tape (fuel+1) s = (.error (.os e),after) := by
  simp only [run,failed]

theorem run_success (schedule : Schedule) (tape : Nat → Raw)
    (s after : State) (secret : Private) (fuel : Nat)
    (drawn : next schedule tape s = (.ok secret.val,after)) :
    run schedule tape (fuel+1) s = (.ok secret,after) := by
  simp only [run,drawn,decode_success]

/-- The context may include all earlier adversary queries and their answers.
The nonce policy is unrestricted on that context. The same context, public
policy, private tape and ledger give exact prefix equality for all ledgers. -/
theorem adaptive_prefix {C : Type} (choose : C → Path) (c d : C) (same : c = d)
    (address : Path → Path) (schedule : Schedule) (tape : Nat → Raw)
    (unix : Bool) (s t : State) (shared : s = t) :
    prepare address (choose c) schedule tape unix s =
      prepare address (choose d) schedule tape unix t := by rw [same,shared]

theorem reservation_uses_public_nonce (address : Path → Path) (nonce : Path)
    (schedule : Schedule) (tape : Nat → Raw) (unix : Bool)
    (s after : State) (secret : Private)
    (generated : generate nonce schedule tape s = (.ok secret,after)) :
    prepare address nonce schedule tape unix s =
      let (result,final) := reserve schedule unix (address nonce) after
      (result.map (fun _ => secret) |>.mapError ProverCommitEnvironment35.Error.reservation,final) := by
  simp only [prepare,generated]

theorem duplicate_stops (address : Path → Path) (nonce : Path)
    (schedule : Schedule) (tape : Nat → Raw) (unix : Bool)
    (s after : State) (secret : Private)
    (generated : generate nonce schedule tape s = (.ok secret,after))
    (occupied : address nonce ∈ after.ledger) :
    (prepare address nonce schedule tape unix s).1 = .error (.reservation .duplicate) := by
  rw [reservation_uses_public_nonce address nonce schedule tape unix s after secret generated]
  have hit := duplicate_path schedule unix (address nonce) after occupied
  simp only [hit,Except.map,Except.mapError]

theorem fail_closed {W P : Type} (address : Path → Path) (nonce : Path)
    (schedule : Schedule) (tape : Nat → Raw) (unix : Bool)
    (s after : State) (e : Error)
    (failed : prepare address nonce schedule tape unix s = (.error e,after))
    (w : W) (real : W → Private → State → Except Error P × State)
    (ideal : Unit → Private → State → Except Error P × State) :
    withPrepared address nonce schedule tape unix s w real =
      withPrepared address nonce schedule tape unix s () ideal := by
  simp only [withPrepared,failed]

/-- Exactly the existing part-39 reservation coupling, now applied to an
arbitrary public nonce rather than a uniformly sampled nonce. -/
theorem public_reservation (address : Path → Path) (nonce : Path)
    (schedule : Schedule) (unix : Bool) (s t : State) (shared : s = t) :
    reserve schedule unix (address nonce) s = reserve schedule unix (address nonce) t :=
  ProverCommitLedgerCoupling39.same_reservation address schedule unix nonce s t shared

/-- Ordered public oracle observations retain repeats and memo hits. -/
def publicReads (rom : List UInt8 → OracleAnswer) (inputs : List (List UInt8)) :=
  inputs.map (fun a => (a,rom a))

theorem public_reads_preserved (real ideal : List UInt8 → OracleAnswer)
    (inputs : List (List UInt8)) (agree : ∀ a ∈ inputs, real a = ideal a) :
    publicReads real inputs = publicReads ideal inputs := by
  apply List.map_congr_left
  intro a ha
  rw [agree a ha]

theorem memo_preserved (rom : List UInt8 → OracleAnswer)
    (a : List UInt8) (value : OracleAnswer) (memo : rom a = value) :
    publicReads rom [a,a] = [(a,value),(a,value)] := by simp [publicReads,memo]

#print axioms zero_guard
#print axioms decode_success
#print axioms run_os_error
#print axioms run_success
#print axioms adaptive_prefix
#print axioms reservation_uses_public_nonce
#print axioms duplicate_stops
#print axioms fail_closed
#print axioms public_reservation
#print axioms public_reads_preserved
#print axioms memo_preserved
end R1Z.ProverCommitPublicNonce40
