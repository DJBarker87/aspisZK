import NFS_QueryLoopRoot
import NGC_Initialization
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_NFW_QueryEntry
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
def zeroQ : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def oneQ : Q := ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def zeroE : E := ⟨zeroQ,zeroQ⟩
def weights : alloc.vec.Vec Q := ⟨List.replicate 64 zeroQ,by simp;scalar_tac⟩
def initial : verifier.Accumulator := ⟨weights,zeroE,oneQ,0#usize⟩
def rowWeights : S8OwnedP6Finish.Weights :=
 ⟨List.replicate 64 ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,by simp;scalar_tac⟩
def pending : verifier.BatchedWeights :=
 ⟨S7Kani3CallerTrace.initialRaw rowWeights,0#usize⟩
/-- The row progress invariant is obtained from the actual initialized carrier,
not requested as an extra query-loop premise. Native constructor binding remains
an explicit producer boundary until its own packet is installed. -/
theorem progress : S7JoinRowsTrace.Progress 0 0 (Port3_RowsInstall.toBW pending) := by
 exact S7JoinQueryRows.initial_progress rowWeights
  (by simp [rowWeights])
theorem power : NBF_PowerStep.Canonical initial.power := by
 intro k
 fin_cases k <;> decide
theorem rhs : NBO_TailDomain.WideCanonical initial.rhs := by
 constructor <;> intro k <;> fin_cases k <;> decide
theorem weights_canonical :
 NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator initial).weights := by
 intro q member
 simp only [NEV_AccumulateCarriers.fromAccumulator,NEV_AccumulateCarriers.mapVec,
  initial,weights,List.mem_map] at member
 obtain ⟨x,hx,rfl⟩ := member
 have eq : x=zeroQ := (List.mem_replicate.mp hx).2
 subst x
 intro k
 fin_cases k <;> decide
/-- Only the Prepared producer's rho fact remains; every initializer fact is
proved for these same concrete caller-owned states. -/
theorem domain (p : verifier.Prepared) (rho : NBF_PowerStep.Canonical p.rho) :
 NFS_QueryInvariant.Domain p 0 10 initial pending := by
 exact ⟨by simp [initial,weights],weights_canonical,rhs,power,rho,progress,rfl,by decide⟩
#print axioms progress
#print axioms power
#print axioms rhs
#print axioms weights_canonical
#print axioms domain
end AspisR1.NGC_NFW_QueryEntry
