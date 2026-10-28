import R1Z.ProverCommitOwnerBytes42

/-! Stateful structural owner bridge. The primitive is the existing byte-blind
schedule/OS model; arbitrary full 64-byte draws remain on the tape. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnerRun42
open Aeneas Aeneas.Std Result AspisR1PublicNonce41
open ProverCommitOwnerZero42 ProverCommitOwnerBytes42
open ProverCommitLedger36
attribute [local instance] Classical.propDecidable
abbrev IOError := ProverCommitEnvironment35.IOError
abbrev NativeStatus := core.result.Result owner.Secret (owner.Error IOError)

def next (schedule : Schedule) (tape : Nat → owner.Raw) (s : State) :
    core.result.Result owner.Raw IOError × State :=
  let (result,after) := ask schedule .rng s
  match result with
  | .error e => (.Err e,after)
  | .ok _ => (.Ok (tape s.cursor),{after with cursor := s.cursor+1})

def io (schedule : Schedule) (tape : Nat → owner.Raw) : owner.IO Unit State IOError where
  fill s := ok (next schedule tape s)

def run (nonce : ProverCommitOwnerZero42.Bytes) (schedule : Schedule) (tape : Nat → owner.Raw) :
    Nat → State → NativeStatus × State
  | 0,s => (.Err .RepeatedZero,s)
  | n+1,s =>
    let (result,after) := next schedule tape s
    match result with
    | .Err e => (.Err (.Os e),after)
    | .Ok r => if block r.field = 0 ∨ block r.leaf = 0 then run nonce schedule tape n after
      else (.Ok ⟨nonce,r⟩,after)

theorem fuel_sub (fuel : U8) (positive : 0 < fuel.val) :
    (U8.wrapping_sub fuel 1#u8).val = fuel.val-1 := by
  rw [U8.wrapping_sub_val_eq]
  simp only [show (1#u8).val=1 from rfl]
  simp only [UScalar.size_def,UScalarTy.U8_numBits_eq]
  have bound := fuel.bv.isLt
  change fuel.val < 256 at bound
  omega

theorem run_exact (nonce : ProverCommitOwnerZero42.Bytes) (schedule : Schedule)
    (tape : Nat → owner.Raw) (n : Nat) (fuel : U8) (s : State) (count : fuel.val=n) :
    owner.run (io schedule tape) nonce fuel s = ok (run nonce schedule tape n s) := by
  induction n generalizing fuel s with
  | zero =>
    have zero : fuel=0#u8 := UScalar.eq_of_val_eq count
    subst fuel
    rw [owner.run]
    rfl
  | succ n ih =>
    have notzero : fuel ≠ 0#u8 := by intro h; subst fuel; change 0=n+1 at count; omega
    have positive : 0<fuel.val := by omega
    have tail := ih (U8.wrapping_sub fuel 1#u8)
    rw [owner.run]
    simp only [notzero,if_false,io,bind_tc_ok]
    rw [run]
    cases step : next schedule tape s with
    | mk result after =>
      cases result with
      | Err e => rfl
      | Ok r =>
        simp only [step,zero_block,bind_tc_ok]
        by_cases hf : block r.field=0
        · simp [hf,lift,bind_tc_ok]
          exact tail after (by rw [fuel_sub fuel positive]; omega)
        · simp [hf]
          by_cases hl : block r.leaf=0
          · simp [hl,lift,bind_tc_ok]
            exact tail after (by rw [fuel_sub fuel positive]; omega)
          · simp [hl]

def generate (nonce : ProverCommitOwnerZero42.Bytes) (schedule : Schedule)
    (tape : Nat → owner.Raw) (s : State) : NativeStatus × State :=
  if block nonce=0 then (.Err .RepeatedZero,s) else run nonce schedule tape 16 s

theorem generate_exact (nonce : ProverCommitOwnerZero42.Bytes) (schedule : Schedule)
    (tape : Nat → owner.Raw) (s : State) :
    owner.generate (io schedule tape) nonce s = ok (generate nonce schedule tape s) := by
  rw [owner.generate,zero_block]
  by_cases hz : block nonce=0
  · simp only [hz,decide_true,if_true,bind_tc_ok,generate]
  · simp only [hz,decide_false,Bool.false_eq_true,if_false,bind_tc_ok,generate]
    exact run_exact nonce schedule tape 16 16#u8 s rfl

#print axioms fuel_sub
#print axioms run_exact
#print axioms generate_exact
end R1Z.ProverCommitOwnerRun42
