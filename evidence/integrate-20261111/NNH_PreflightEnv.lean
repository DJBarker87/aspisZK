import NNH_HostEnv
set_option autoImplicit false
namespace AspisR1.NNH_PreflightEnv
open RSL
#print RSL.Env
/-- All four components are pinned by the existing representation predicate. -/
theorem unique (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (reservation : NP6_StdModel.Reservation)
 (env : Env) (h : NNH_HostEnv.EnvRep sha pda clock reservation env) :
 env = NNH_HostEnv.environment sha pda clock reservation := by
 rcases env with ⟨s,p,c,r⟩
 rcases h with ⟨hs,hp,hc,hr⟩
 have he : r = NNH_HostEnv.reserveOK reservation := by
  cases r <;> cases reservation with
  | Ok u => cases u <;> simp_all only [NNH_HostEnv.reserveOK, Bool.false_eq_true,
      Bool.true_eq_false, iff_false, iff_true, not_true_eq_false]
  | Err e => simp_all only [NNH_HostEnv.reserveOK, reduceCtorEq, iff_false,
      Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false]
 cases hs; cases hp; cases hc; cases he
 rfl
#print axioms unique
end AspisR1.NNH_PreflightEnv
