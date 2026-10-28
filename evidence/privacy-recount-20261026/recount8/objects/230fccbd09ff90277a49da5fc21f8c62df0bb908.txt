import R1Z.ProverCommitEntropyJoin18
import R0Z.AbsorptionLaw
/-! Successful bounded entropy draws are symmetric under every permutation
of the nonzero-secret carrier, assuming uniform raw draws. Failure remains
in the law. This is not an assumption of uniform/error-free OS behaviour. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEntropySymmetry18
open R0Z R1Z.GamesR1PBin R1Z.ProverCommitEntropy18 R1Z.ProverCommitEntropyJoin18
attribute [local instance] Classical.propDecidable

def erase (secret : SecP) : Candidate := fun i => (secret i).val

theorem erase_of_decode (raw : Candidate) (secret : SecP)
    (decoded : decode raw = some secret) : erase secret = raw := by
  unfold decode at decoded
  split at decoded
  · cases Option.some.inj decoded
    rfl
  · cases decoded

def lift (e : SecP ≃ SecP) (raw : Candidate) : Candidate :=
  match decode raw with
  | none => raw
  | some secret => erase (e secret)

theorem decode_erase (secret : SecP) : decode (erase secret) = some secret :=
  decode_success secret

theorem lift_erase (e : SecP ≃ SecP) (secret : SecP) :
    lift e (erase secret) = erase (e secret) := by
  simp only [lift, decode_erase]

theorem decode_lift (e : SecP ≃ SecP) (raw : Candidate) :
    decode (lift e raw) = (decode raw).map e := by
  cases hd : decode raw with
  | none => simp only [lift, hd, Option.map_none]
  | some secret => simp only [lift, hd, decode_erase, Option.map_some]

def rawEquiv (e : SecP ≃ SecP) : Candidate ≃ Candidate where
  toFun := lift e
  invFun := lift e.symm
  left_inv := by
    intro raw
    cases hd : decode raw with
    | none => simp only [lift, hd]
    | some secret =>
      change lift e.symm (lift e raw) = raw
      have hLift : lift e raw = erase (e secret) := by simp only [lift, hd]
      rw [hLift, lift_erase, e.symm_apply_apply, erase_of_decode raw secret hd]
  right_inv := by
    intro raw
    cases hd : decode raw with
    | none => simp only [lift, hd]
    | some secret =>
      change lift e (lift e.symm raw) = raw
      have hLift : lift e.symm raw = erase (e.symm secret) := by simp only [lift, hd]
      rw [hLift, lift_erase, e.apply_symm_apply, erase_of_decode raw secret hd]

def mapDraw {State OsError : Type} (e : SecP ≃ SecP)
    (next : State → Except OsError Candidate × State)
    (state : State) : Except OsError Candidate × State :=
  ((next state).1.map (lift e), (next state).2)

/-- The same draw positions and state history are retained on both sides;
only valid candidates are permuted. OS failure and zero rejection are fixed. -/
theorem run_equivariant {State OsError : Type} (e : SecP ≃ SecP)
    (next : State → Except OsError Candidate × State) (fuel : Nat) (state : State) :
    run (mapDraw e next) fuel state =
      ((run next fuel state).1.map e, (run next fuel state).2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases hn : next state with | mk status after =>
      cases status with
      | error error => simp only [run, mapDraw, hn, Except.map]
      | ok raw =>
        simp only [run, mapDraw, hn, Except.map]
        rw [decode_lift]
        cases hd : decode raw with
        | none =>
          simp only [Option.map_none]
          exact ih after
        | some secret => rfl

def drawsEquiv (e : SecP ≃ SecP) : RawRand ≃ RawRand :=
  Equiv.piCongrRight (fun _ => rawEquiv e)

theorem rawGenerate_equivariant (e : SecP ≃ SecP) (raw : RawRand) :
    rawGenerate (drawsEquiv e raw) = (rawGenerate raw).map e := by
  have next : rawNext (drawsEquiv e raw) = mapDraw e (rawNext raw) := rfl
  unfold rawGenerate generate
  rw [next, run_equivariant]

/-- Every two successful secrets have exactly the same mass in the
unconditioned 16-draw experiment. No rejected draw is erased from the law. -/
theorem successful_law_equal (a b : SecP) :
    law rawGenerate (Except.ok a) = law rawGenerate (Except.ok b) := by
  let e := Equiv.swap a b
  have transported := AbsorptionLaw.law_equiv (drawsEquiv e) rawGenerate (Except.ok b)
  have pointwise (raw : RawRand) :
      rawGenerate (drawsEquiv e raw) = Except.ok b ↔ rawGenerate raw = Except.ok a := by
    rw [rawGenerate_equivariant]
    cases hr : rawGenerate raw with
    | error error => constructor <;> intro impossible <;> cases impossible
    | ok secret =>
      simp only [Except.map, Except.ok.injEq]
      change e secret = b ↔ secret = a
      rw [Equiv.apply_eq_iff_eq_symm_apply]
      simp only [e, Equiv.symm_swap, Equiv.swap_apply_right]
  calc
    law rawGenerate (Except.ok a) =
        law (fun raw => rawGenerate (drawsEquiv e raw)) (Except.ok b) := by
      unfold law
      congr 1
      funext raw
      rw [pointwise]
    _ = law rawGenerate (Except.ok b) := transported

#print axioms erase_of_decode
#print axioms decode_erase
#print axioms lift_erase
#print axioms decode_lift
#print axioms run_equivariant
#print axioms rawGenerate_equivariant
#print axioms successful_law_equal
end R1Z.ProverCommitEntropySymmetry18
