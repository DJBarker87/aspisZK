import NNH_HostEnv
set_option autoImplicit false
namespace AspisR1.NNH_EnvUnique
open RSL NNH_HostEnv
/-- Rev3's reservation conjunct determines the Boolean on both runtime arms. -/
theorem reservation (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : Env) (h : EnvRep sha pda clock r env) : env.reservation=reserveOK r := by
 apply Bool.eq_iff_iff.mpr
 rw [reserveOK_iff]
 exact h.2.2.2

/-- Every represented environment is exactly the same runtime environment.
No successful reservation or hash totality premise is introduced. -/
theorem unique (sha : List Bytes → B32) (pda : List Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : Env) (h : EnvRep sha pda clock r env) : env=environment sha pda clock r := by
 have res := reservation sha pda clock r env h
 obtain ⟨hsha,hpda,hclock,_⟩ := h
 cases env
 simp only [environment,Env.mk.injEq]
 exact ⟨hsha,hpda,hclock,res⟩

/-- Pointwise use with an installed TAS signature, preserving its exact c. -/
theorem installed (S : TAS.Sig) (r : Runtime S.Ctx) (c : S.Ctx)
 (env : Env) (rep : (NNH_HostEnv.install S r).EnvRep c env) :
 env=(NNH_HostEnv.install S r).env2 c :=
 unique (r.sha c) (r.pda c) (r.clock c) (r.reservation c) env rep

#print axioms reservation
#print axioms unique
#print axioms installed
end AspisR1.NNH_EnvUnique
