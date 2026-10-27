import Tx2N_Powers
import RPu_FJi_MatchingMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_SelectedPowers
open Aeneas Aeneas.Std Result
abbrev E := FIp_DotsAdapter.E
theorem decode (x : E) : AspisR1LoopPowers.decode (Tx2N_Powers.toPowers x)=CheckpointBytes5Output.ofE x := by
  change AspisR1CurrentWide.Proof.decodeWide (SAQ_WideABI.toW x)=_
  exact SAQ_WideABI.w_decode x
/-- The actual constructor's successful result is the SAME g used below. -/
theorem value (gamma : E) (g : Array E 29#usize)
    (canonical : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers gamma))
    (run : Tx2N_Powers.powers 29#usize gamma=ok g) :
    FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g) ∧
      ∀ j : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) j.val=
        CheckpointBytes5Output.ofE gamma^j.val := by
  obtain ⟨out,hr,hv⟩ := Tx2N_Powers.total_exact 29#usize gamma canonical
  have same := Result.ok.inj (hr.symm.trans run)
  subst out
  have hcanon : ∀ j : Fin 29,FIo_WideValues.Canon
      (FIo_Install.toE (g.val[j.val]'(by rw [g.property];exact j.isLt))) := by
    intro j
    have h := (hv j).1
    change ((_ ∧ _) ∧ (_ ∧ _)) ∧ ((_ ∧ _) ∧ (_ ∧ _)) at h
    exact h
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp hy
    have hi : n < 29 := by
      rw [g.property] at hn
      have v29 : (29#usize).val=29 := by scalar_tac
      simpa only [v29] using hn
    simpa only [eq] using hcanon ⟨n,hi⟩
  · intro j
    have h := (hv j).2
    unfold FIp_ArrayValue.value FIp_DotsAdapter.toArray
    rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [g.property];exact j.isLt)]
    rw [decode,decode] at h
    exact (SAQ_WideABI.w_decode _).trans h
#print axioms decode
#print axioms value
end AspisR1.FJi_SelectedPowers
end
