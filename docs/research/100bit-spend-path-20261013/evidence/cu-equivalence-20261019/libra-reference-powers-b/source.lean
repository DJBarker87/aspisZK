import CuSavingsLibraSourceModel
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraReferencePowers
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
open CuSavingsLibraSourceHandback (reference_power_callback referenceRaw)
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

abbrev Powers := Array K 28#usize
abbrev Extra := Array K 2#usize
abbrev PowerClosure := K × Extra × Usize

theorem callback (power : K) (extra : Extra) (side index : Usize) :
    (old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31).call_mut
      (power,extra,side) index =
      (do let q ← Array.index_usize extra side
          let product ← field.QM31.mul power q
          .ok (power,(product,extra,side))) := by
  change old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    (power,extra,side) index = _
  rw [reference_power_callback]
  change (do let (value,state,back) ← referenceRaw power extra side
             .ok (value,back state)) = _
  unfold referenceRaw
  cases h : Array.index_usize extra side with
  | fail e => rfl
  | div => rfl
  | ok q =>
    simp only [h,bind_tc_ok]
    cases hm : field.QM31.mul power q <;> simp only [hm,bind_tc_ok,bind_tc_fail,bind_tc_div] <;> rfl

theorem side_success (extra : Extra) (side : Usize) (hs : side.val<2)
    (he : A.canonicalK (lookup extra field.QM31.ONE side.val)) :
    ∃ powers,
      old.twofold_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayQM3128.call_mut
        extra side=.ok (powers,extra) ∧
      ∀ i (hi : i<28),
        A.canonicalK (powers.val[i]'(by rw [powers.property];exact hi)) ∧
        A.decodeK (powers.val[i]'(by rw [powers.property];exact hi))=
          (A.decodeK (lookup extra field.QM31.ONE side.val))^i := by
  let q := lookup extra field.QM31.ONE side.val
  let inst := old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  let P : Nat → PowerClosure → Prop := fun j state =>
    A.canonicalK state.1 ∧ state.2.1=extra ∧ state.2.2=side ∧ A.decodeK state.1=(A.decodeK q)^j
  let V : Nat → K → Prop := fun j value => A.canonicalK value ∧ A.decodeK value=(A.decodeK q)^j
  have hread := read extra field.QM31.ONE side (by simpa using hs)
  have hstep : ∀ j state index, j<28 → index.val=j → P j state →
      ∃ value state1, inst.call_mut state index=.ok (value,state1) ∧ V j value ∧ P (j+1) state1 := by
    intro j state index _ _ hp
    rcases state with ⟨power,extra1,side1⟩
    rcases hp with ⟨hpower,hextra,hside,hvalue⟩
    change extra1=extra at hextra
    change side1=side at hside
    change A.canonicalK power at hpower
    change A.decodeK power=(A.decodeK q)^j at hvalue
    subst extra1
    subst side1
    obtain ⟨product,hproduct,hcanonical,hdecode⟩ := A.kmul power q hpower he
    refine ⟨power,(product,extra,side),?_,⟨hpower,hvalue⟩,hcanonical,rfl,rfl,?_⟩
    · change (old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31).call_mut
        (power,extra,side) index=.ok (power,(product,extra,side))
      rw [callback,hread,hproduct]
      rfl
    · simpa only [hvalue,pow_succ] using hdecode
  have initial : P 0 (field.QM31.ONE,extra,side) := ⟨A.one,rfl,rfl,by simpa only [pow_zero] using A.one_value⟩
  obtain ⟨values,finalState,hcells,hvalues,_⟩ :=
    CuSavingsLibraSourceBuilder.cells_success inst P V 28 hstep 28 0#usize
      (field.QM31.ONE,extra,side) initial (by scalar_tac) (by scalar_tac)
  let powers : Powers := ⟨values.val,values.property⟩
  refine ⟨powers,?_,?_⟩
  · unfold old.twofold_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayQM3128.call_mut
      AspisR1Libra.core.array.from_fn_mut
    dsimp only [inst] at hcells
    simp only [UScalar.ofNatCore_val_eq]
    rw [hcells]
    rfl
  · intro i hi
    simpa only [powers,V,show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hvalues i hi

private theorem lookup_get {T : Type} {N : Usize} (array : Array T N) (default : T)
    (i : Nat) (hi : i<N.val) :
    lookup array default i=array.val[i]'(by rw [array.property];exact hi) := by
  exact List.getD_eq_getElem array.val default (by rw [array.property];exact hi)

def Valid (powers : Array Powers 2#usize) (extra : Extra) : Prop :=
  ∀ side, side<2 → ∀ i, i<28 →
    A.canonicalK (lookup (lookup powers (Array.repeat 28#usize field.QM31.ONE) side) field.QM31.ONE i) ∧
    A.decodeK (lookup (lookup powers (Array.repeat 28#usize field.QM31.ONE) side) field.QM31.ONE i)=
      (A.decodeK (lookup extra field.QM31.ONE side))^i

theorem source_success (extra : Extra)
    (he : ∀ side, side<2 → A.canonicalK (lookup extra field.QM31.ONE side)) :
    ∃ powers : Array Powers 2#usize,
      AspisR1Libra.core.array.from_fn 2#usize
        old.twofold_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayQM3128 extra=.ok powers ∧
      Valid A powers extra := by
  let inst := old.twofold_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayQM3128
  let P : Nat → Extra → Prop := fun _ state => state=extra
  let V : Nat → Powers → Prop := fun side value => ∀ i (hi : i<28),
    A.canonicalK (value.val[i]'(by rw [value.property];exact hi)) ∧
    A.decodeK (value.val[i]'(by rw [value.property];exact hi))=(A.decodeK (lookup extra field.QM31.ONE side))^i
  have hstep : ∀ j state index, j<2 → index.val=j → P j state →
      ∃ value state1, inst.call_mut state index=.ok (value,state1) ∧ V j value ∧ P (j+1) state1 := by
    intro j state index hj hindex hp
    change state=extra at hp
    subst state
    obtain ⟨value,hvalue,hv⟩ := side_success A extra index (by omega) (by simpa only [hindex] using he j hj)
    refine ⟨value,extra,hvalue,?_,rfl⟩
    simpa only [V,hindex] using hv
  obtain ⟨values,finalState,hcells,hvalues,_⟩ :=
    CuSavingsLibraSourceBuilder.cells_success inst P V 2 hstep 2 0#usize extra rfl
      (by scalar_tac) (by scalar_tac)
  let powers : Array Powers 2#usize := ⟨values.val,values.property⟩
  refine ⟨powers,?_,?_⟩
  · unfold AspisR1Libra.core.array.from_fn CuSavingsArrayBuilder.build
    dsimp only [inst] at hcells
    simp only [UScalar.ofNatCore_val_eq]
    rw [hcells]
    rfl
  · intro side hs i hi
    have hv := hvalues side hs i hi
    rw [lookup_get powers (Array.repeat 28#usize field.QM31.ONE) side (by simpa using hs),
      lookup_get _ field.QM31.ONE i (by simpa using hi)]
    simpa only [powers,V,show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hv

#print axioms callback
#print axioms side_success
#print axioms source_success
end AspisR1.CuSavingsLibraReferencePowers
