import AspisR1RhoPowerTail.Funs

/-! Actual byte-identical power/counter suffix from old/new accumulation.
Canonical power is preserved by the exact existing QM31 multiplication; no
child-call success premise is used. This is not yet the complete caller. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoPowerTail
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail

abbrev Canonical (x : aspis_core.field.QM31) : Prop :=
  ExtractedCurrentTowerAdd.CanonicalQM (toCurrent x)

theorem to_from (x : Current) : toCurrent (fromCurrent x) = x := rfl

theorem from_to (x : aspis_core.field.QM31) : fromCurrent (toCurrent x) = x := rfl

theorem next_success (index : Usize) (h : index.val < 22) :
    ∃ next : Usize,(index+1#usize : Result Usize) = .ok next ∧
      next.val=index.val+1 := by
  have hone : (1#usize).val = 1 := by scalar_tac
  have hmax : index.val+(1#usize).val ≤ UScalar.max .Usize := by
    have hlarge : 22 ≤ UScalar.max .Usize := by scalar_tac
    rw [hone]
    omega
  obtain ⟨next,hadd,hval⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=index) (y:=1#usize) hmax)
  exact ⟨next,hadd,by simpa only [hone] using hval⟩

/-- Exact whole suffix outcome, including multiplication/addition failure and
 divergence. The successful state frame is the original source record update. -/
theorem source_outcome (p : verifier.Prepared) (a : verifier.Accumulator) :
    power_tail p a = (do
      let q ← aspis_core.field.QM31.mul a.power p.rho
      let next ← a.next+1#usize
      pure {a with power:=q,next:=next}) := rfl

theorem source_success (p : verifier.Prepared) (a : verifier.Accumulator)
    (hp : Canonical a.power) (hr : Canonical p.rho) (hn : a.next.val < 22) :
    ∃ out : verifier.Accumulator,
      power_tail p a = .ok out ∧ Canonical out.power ∧
      out.next.val=a.next.val+1 ∧ out.next.val ≤ 22 ∧
      out.weights=a.weights ∧ out.rhs=a.rhs ∧
      ExtractedCurrentQM31Mul.wordsQM (toCurrent out.power) =
        ExtractedCurrentQM31Mul.qmMulWords
          (ExtractedCurrentQM31Mul.wordsQM (toCurrent a.power))
          (ExtractedCurrentQM31Mul.wordsQM (toCurrent p.rho)) := by
  obtain ⟨q,hm,hq,hwords⟩ := ExtractedCurrentQM31Mul.current_qm_mul_words
    (toCurrent a.power) (toCurrent p.rho) hp hr
  obtain ⟨next,hadd,hval⟩ := next_success a.next hn
  let out : verifier.Accumulator := {a with power:=fromCurrent q,next:=next}
  refine ⟨out,?_,?_,hval,(by change next.val ≤ 22; omega),rfl,rfl,?_⟩
  · simp only [power_tail,aspis_core.field.QM31.mul,hm,bind_tc_ok,hadd,out] <;> rfl
  · exact hq
  · exact hwords

#print axioms to_from
#print axioms from_to
#print axioms next_success
#print axioms source_outcome
#print axioms source_success
end AspisR1.CuSavingsRhoPowerTail
