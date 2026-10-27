import LPq_PreparedTrace
set_option autoImplicit false
namespace AspisR1.LPq_PreparedClaim
open Aeneas Aeneas.Std Result LPi_FieldValues
open AspisR1CurrentPreparedClaim

/-- Frozen source has no digest invocation in this leaf. This function family
keeps the nominal digest instance arbitrary rather than specializing to one
reply or one native successful output. Native association remains the hybrid
local-gate/source-partition obligation documented in the leaf packet. -/
def program {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (inactive kappa : NE) :=
  fun inst : aspis_core.Digest32 H => verifier.prepared_claim LPm_PointLoop.ops inst
    sem y1 (LPq_Powers.claim inactive) g (LPq_Powers.claim kappa)

theorem program_eq {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array Concrete.E 29#usize} {inactive kappa out : NE}
    (hi : canonE inactive) (hk : canonE kappa)
    (tr : LPq_PreparedTrace.Trace sem y1 g inactive kappa out) :
    program sem y1 g inactive kappa = fun _ => ok (.Ok (LPq_Powers.claim out)) := by
  funext inst
  exact LPq_PreparedTrace.source inst hi hk tr

/-- ONE constructed local trace supplies the SAME result for every digest
instance. No accepted whole-body run, whole-output equality or independent
final array is a premise. SelectedFields is still explicit in this interface. -/
theorem native_result {H : Type} (sem : r1_semantic.Verified H)
    (hs : LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : LPq_SixPoints.SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : LPq_ReadPorts.WeightsCanonical g)
    (inactive kappa : NE) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ out, LPq_PreparedTrace.Trace sem y1 g inactive kappa out ∧ canonE out ∧
      program sem y1 g inactive kappa = fun _ => ok (.Ok (LPq_Powers.claim out)) := by
  obtain ⟨out,tr,co⟩ := LPq_PreparedTrace.construct sem hs y1 hy g hg inactive kappa hi hk
  exact ⟨out,tr,co,program_eq hi hk tr⟩

theorem uniqueness {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {inactive kappa left right : NE} (hi : canonE inactive) (hk : canonE kappa)
    (lt : LPq_PreparedTrace.Trace sem y1 g inactive kappa left)
    (rt : LPq_PreparedTrace.Trace sem y1 g inactive kappa right) :
    LPq_Powers.claim left=LPq_Powers.claim right := by
  have l := LPq_PreparedTrace.source inst hi hk lt
  have r := LPq_PreparedTrace.source inst hi hk rt
  exact core.result.Result.Ok.inj (Result.ok.inj (l.symm.trans r))

#print axioms program_eq
#print axioms native_result
#print axioms uniqueness
end AspisR1.LPq_PreparedClaim
