import R1Z.SimCostRelativeIdeal

/-! A remaining signature obstruction, with the quantifiers made explicit.
The protocol headline permits unbounded public handles and an arbitrary
public-output callback. Fixing that callback still does not give a uniform
cost bound over all statements from adversary query length alone. This does
NOT refute a per-fixed-statement bound, or a bound including public output
size. It prevents treating the metadata stage as already certified. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostRelativeObstruction
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.RefPayload R1Z.Batched
  R1Z.GamesR1 R1Z.SimCostWriter R1Z.SimCostRelativeReplay
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis

/-- A real byte-output loop: each emitted byte costs one tick. -/
def emit : List UInt8 → Costed (List UInt8)
  | [] => ([],0)
  | b::bs => let r := emit bs; (b::r.1,r.2+1)

theorem emit_erase (bs : List UInt8) : (emit bs).1 = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [emit, ih]

theorem emit_cost (bs : List UInt8) : (emit bs).2 = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [emit, ih, List.length_cons]

/-- One fixed public-output callback, not a new callback chosen per bound. -/
def outputs : Statement K Nat → Challenges K → List UInt8 :=
  fun x _ => List.replicate x.2 0

theorem output_cost (π : Fin 1024 ≃ Fin 1024)
    (x : Statement K Nat) (ch : Challenges K) (t : Tape K F) :
    (emit ((simE (Bat := R1Bat) π B outputs x ch t).1.publicOutputs)).2 = x.2 := by
  rw [emit_cost]
  exact List.length_replicate

/-- Fixed field, basis, callback, public field component and adversary (.done).
No fixed polynomial in adversary input alone bounds this metadata byte stage
uniformly over the headline's allowed public handles. K0 denotes the additive
constant in the proposed efficiency bound, not the field type. -/
theorem no_uniform_relative_metadata (π : Fin 1024 ≃ Fin 1024)
    (pub : R0P.Public K) (ch : Challenges K) (t : Tape K F)
    (q c K0 d : Nat) :
    ∃ x : Statement K Nat,
      x.1 = pub ∧ c * (inputLength (fun _ => 0) OProg.done q + K0)^d <
        (emit ((simE (Bat := R1Bat) π B outputs x ch t).1.publicOutputs)).2 := by
  refine ⟨(pub,c*(q+K0)^d+1), rfl, ?_⟩
  rw [output_cost]
  simp only [inputLength, queryBytes, Nat.add_zero]
  exact Nat.lt_succ_self _

#print axioms emit_erase
#print axioms emit_cost
#print axioms output_cost
#print axioms no_uniform_relative_metadata
end R1Z.SimCostRelativeObstruction
