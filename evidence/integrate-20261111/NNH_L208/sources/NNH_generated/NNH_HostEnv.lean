import RSL_Base
import RPx_Deployed
set_option autoImplicit false
namespace AspisR1.NNH_HostEnv
open RSL

/-- The single headline reservation reply, including its returned Err arm. -/
def reserveOK : NP6_StdModel.Reservation → Bool
 | .Ok () => true
 | .Err _ => false

/-- Host runtime agreement. The reservation conjunct is required by RSL rev3.
The oracle arguments are retained runtime replies, not assertions of success. -/
def EnvRep (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (reservation : NP6_StdModel.Reservation)
 (env : Env) : Prop :=
 env.sha256 = sha ∧ env.pda = pda ∧ env.clock = clock ∧
 (env.reservation = true ↔ reservation = .Ok ())

/-- Both transaction environments use the same headline reservation binder.
TX2 supplies its actual clock reply; TX1 may use the unused-clock error. -/
def environment (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (reservation : NP6_StdModel.Reservation) : Env :=
 ⟨sha, pda, clock, reserveOK reservation⟩

theorem reserveOK_iff (reservation : NP6_StdModel.Reservation) :
 reserveOK reservation = true ↔ reservation = .Ok () := by
 cases reservation with
 | Ok u => cases u; exact ⟨fun _ => rfl, fun _ => rfl⟩
 | Err e => simp only [reserveOK, Bool.false_eq_true, reduceCtorEq]

theorem environment_rep (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (reservation : NP6_StdModel.Reservation) :
 EnvRep sha pda clock reservation (environment sha pda clock reservation) :=
 ⟨rfl, rfl, rfl, reserveOK_iff reservation⟩

theorem reservation_binding (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (reservation : NP6_StdModel.Reservation)
 (env : Env) (h : EnvRep sha pda clock reservation env) :
 env.reservation = true ↔ reservation = .Ok () := h.2.2.2

#print axioms reserveOK_iff
#print axioms environment_rep
#print axioms reservation_binding
end AspisR1.NNH_HostEnv
