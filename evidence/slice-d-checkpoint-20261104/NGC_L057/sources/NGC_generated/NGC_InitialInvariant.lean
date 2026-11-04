import NGC_NFW_QueryEntry
import NGC_PreparationBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_InitialInvariant
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Relates the SAME emitted constructor results to NFW's committed initial
carrier. Native pending-constructor binding remains an explicit boundary. -/
theorem initial (base : VTop_Stages.Ops) (reserveA reserveB : Bool)
 (p : verifier.Prepared) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (prepared : NGC_PreparationBoundary.Fields p)
 (newA : (Port3_Constructor.installed base reserveA).op12 .S2=ok (.Ok a))
 (newB : Port3_NativePendingInstall.source reserveB a.weights.deref=ok (.Ok b)) :
 NFS_QueryInvariant.Domain p 0 10 a b ∧ a.next.val=0 := by
 obtain ⟨_,weights,rhs,power,next⟩ := NGC_Initialization.accepted base reserveA a newA
 have width : a.weights.val.length=64 := by rw [weights,List.length_replicate]
 have pending := Port3_NativePendingInstall.accepted_fields reserveB a.weights.deref b width newB
 have aeq : a=NGC_NFW_QueryEntry.initial := by
  cases a with
  | mk w r po n =>
   have hw : w=NGC_NFW_QueryEntry.weights := Subtype.ext weights
   cases hw
   cases rhs
   cases power
   cases next
   rfl
 subst a
 have raw : b.raw=NGC_NFW_QueryEntry.pending.raw := by
  apply Subtype.ext
  rw [pending.2.1]
  simp only [NGC_NFW_QueryEntry.initial,NGC_NFW_QueryEntry.weights,
   NGC_NFW_QueryEntry.pending,NGC_NFW_QueryEntry.rowWeights,
   S7Kani3CallerTrace.initialRaw,List.map_replicate]
  rfl
 have beq : b=NGC_NFW_QueryEntry.pending := by
  cases b with
  | mk r t =>
   cases raw
   cases pending.2.2.1
   rfl
 subst b
 exact ⟨NGC_NFW_QueryEntry.domain p prepared.rho,rfl⟩
#print axioms initial
end AspisR1.NGC_InitialInvariant
end
