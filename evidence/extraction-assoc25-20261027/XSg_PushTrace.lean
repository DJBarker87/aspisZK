import XSg_Sweep
import XRz_PushReach
import XSe_PowerDomain
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
noncomputable section
namespace XSg_PushTrace
open S7Kani3CallerTrace S7Kani2OwnedRowRefinement
/-- A source push on the current unprocessed cursor derives the old trace
extension's phase premise from the actual sweep invariant. -/
theorem source (old : S8OwnedP6Finish.Weights) (b out : verifier.BatchedWeights) (sum : Sum)
 (history : PushTrace old (XRu_PushTransport.bw b) sum)
 (i : Usize) (q : aspis_core.field.QM31) (m : U32)
 (bound : i.val<b.raw.length) (canonical : XRp_PowersQAdd.CanonicalQ q)
 (bm : m.val<2^31-1) (phase : XSg_Sweep.Inv b.terms.val i.val b.raw)
 (run : verifier.BatchedWeights.push b i q m=ok out) :
 PushTrace old (XRu_PushTransport.bw out)
  (Function.update sum i.val (fun k => sum i.val k+(powerLimb (XRu_PushTransport.power q) k).val*m.val)) := by
 obtain ⟨row,hread,hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b.raw i bound)
 obtain ⟨a,c,d,e,shape⟩ := XRu_RowShape.cells row
 let x : Fin 4 → U64 := fun k => if k=0 then a else if k=1 then c else if k=2 then d else e
 have shaped : row=makeRow x := by rw [shape];rfl
 have get : b.raw.val[i.val]?=some row := by
  rw [List.getElem?_eq_getElem bound];exact congrArg some hval.symm
 have rawBound : XSg_RowPhase.Bound b.terms.val row := by
  simpa only [Nat.lt_irrefl,if_false] using phase i.val row get
 have xp : ∀ k, S7Kani3PhaseInvariant.Phase b.terms.val (x k).val := by
  intro k
  have mem : x k∈row.val := by rw [shaped];fin_cases k <;> simp [makeRow,x]
  exact rawBound (x k) mem
 rw [shaped] at get
 obtain ⟨after,hafter,trace⟩ := XRz_PushReach.source old b sum history i q m x bound get
  (XSe_PowerDomain.source q canonical) bm xp
 cases Result.ok.inj (hafter.symm.trans run)
 exact trace
#print axioms source
end XSg_PushTrace
