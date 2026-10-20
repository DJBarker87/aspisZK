import CuSavingsLibraSourceModel
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourcePowers
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel
open CuSavingsLibraSourceHandback (power_callback powerRaw)
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

/-- Normalization of the actual source callback, after applying its emitted
mutable-capture handback; the final multiplication is retained. -/
theorem callback {N : Usize} (power q : K) (i : Usize) :
    (kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N).call_mut (power,q) i =
      (do let product ← field.QM31.mul power q
          .ok (power,(product,q))) := by
  change kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once (power,q) i = _
  rw [power_callback]
  change (do let (value,state,back) ← powerRaw power q
             .ok (value,back state)) = _
  unfold powerRaw
  cases h : field.QM31.mul power q <;> simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div] <;> rfl

theorem source_success (N : Usize) (q : K) (hq : A.canonicalK q)
    (hN : N.val<Usize.size) :
    ∃ powers, kpowers N q=.ok powers ∧
      ∀ i (hi : i<N.val),
        A.canonicalK (powers.val[i]'(by rw [powers.property];exact hi)) ∧
        A.decodeK (powers.val[i]'(by rw [powers.property];exact hi))=(A.decodeK q)^i := by
  let inst := kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N
  let P : Nat → kpowers.closure N → Prop := fun j state =>
    A.canonicalK state.1 ∧ state.2=q ∧ A.decodeK state.1=(A.decodeK q)^j
  let V : Nat → K → Prop := fun j value => A.canonicalK value ∧ A.decodeK value=(A.decodeK q)^j
  have hstep : ∀ j state index, j<N.val → index.val=j → P j state →
      ∃ value state1, inst.call_mut state index=.ok (value,state1) ∧ V j value ∧ P (j+1) state1 := by
    intro j state index _ _ hp
    rcases state with ⟨power,base⟩
    rcases hp with ⟨hpower,hbase,hvalue⟩
    change base=q at hbase
    change A.canonicalK power at hpower
    change A.decodeK power=(A.decodeK q)^j at hvalue
    subst base
    obtain ⟨product,hproduct,hcanonical,hdecode⟩ := A.kmul power q hpower hq
    refine ⟨power,(product,q),?_,⟨hpower,hvalue⟩,hcanonical,rfl,?_⟩
    · simpa only [inst,callback,hproduct,bind_tc_ok] using
        (rfl : Result.ok (power,(product,q))=Result.ok (power,(product,q)))
    · simpa only [hvalue,pow_succ] using hdecode
  have initial : P 0 (field.QM31.ONE,q) := ⟨A.one,rfl,by simpa only [pow_zero] using A.one_value⟩
  obtain ⟨values,finalState,hcells,hvalues,_⟩ :=
    CuSavingsLibraSourceBuilder.cells_success inst P V N.val hstep N.val 0#usize
      (field.QM31.ONE,q) initial (by simp) hN
  let powers : Array K N := ⟨values.val,values.property⟩
  refine ⟨powers,?_,?_⟩
  · unfold kpowers AspisR1Libra.core.array.from_fn_mut
    dsimp only [inst] at hcells
    rw [hcells]
    rfl
  · intro i hi
    simpa only [powers,V,show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hvalues i hi

#print axioms callback
#print axioms source_success
end AspisR1.CuSavingsLibraSourcePowers
