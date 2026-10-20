import CuSavingsLibraReferenceLoop
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraReference
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
open CuSavingsLibraReferencePowers (Powers Extra)
open CuSavingsLibraReferenceLoop (Low Tables block)
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)
abbrev Closure := Low × Tables
set_option allowUnsafeReducibility true
attribute [local reducible] old.twofold_libra_weights.closure_1

private theorem builder_success {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F)
    (values : {xs : List T // xs.length=N.val}) (finalState : F)
    (h : CuSavingsArrayBuilder.cells inst N.val 0#usize state=.ok (values,finalState)) :
    AspisR1Libra.core.array.from_fn N inst state=.ok ⟨values.val,values.property⟩ := by
  unfold AspisR1Libra.core.array.from_fn CuSavingsArrayBuilder.build
  rw [h]
  rfl

private theorem lookup_get {T : Type} {N : Usize} (array : Array T N) (default : T)
    (i : Nat) (hi : i<N.val) :
    lookup array default i=array.val[i]'(by rw [array.property];exact hi) := by
  exact List.getD_eq_getElem array.val default (by rw [array.property];exact hi)

theorem array_success (low : Low) (powers : Tables) (extra : Extra)
    (hlow : ∀ s, s<16 → A.canonicalE (lookup low field.wide_exact.WideExact.ZERO s))
    (hpowers : CuSavingsLibraReferencePowers.Valid A powers extra) :
    ∃ weights : Array E 4#usize,
      AspisR1Libra.core.array.from_fn 4#usize
        old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (low,powers)=.ok weights ∧
      ∀ j, j<4 → A.canonicalE (lookup weights field.wide_exact.WideExact.ZERO j) ∧
        A.decodeE (lookup weights field.wide_exact.WideExact.ZERO j)=block A low extra j := by
  let inst := old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
  let P : Nat → Closure → Prop := fun _ state => state=(low,powers)
  let V : Nat → E → Prop := fun j value => A.canonicalE value ∧ A.decodeE value=block A low extra j
  have hstep : ∀ j state index, j<4 → index.val=j → P j state →
      ∃ value state1, inst.call_mut state index=.ok (value,state1) ∧ V j value ∧ P (j+1) state1 := by
    intro j state index hj hindex hp
    change state=(low,powers) at hp
    subst state
    obtain ⟨value,hloop,hcanonical,hdecode⟩ :=
      CuSavingsLibraReferenceLoop.source_success A low powers extra index (by omega) hlow hpowers
    refine ⟨value,(low,powers),?_,⟨hcanonical,?_⟩,rfl⟩
    · change old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (low,powers) index=.ok (value,(low,powers))
      change (do
        let out ← old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop
          {start:=0#usize,«end»:=16#usize} low powers index field.wide_exact.WideExact.ZERO
        .ok (out,(low,powers)))=.ok (value,(low,powers))
      rw [hloop]
      rfl
    · simpa only [hindex] using hdecode
  obtain ⟨values,finalState,hcells,hvalues,_⟩ :=
    CuSavingsLibraSourceBuilder.cells_success inst P V 4 hstep 4 0#usize
      (low,powers) rfl (by scalar_tac) (by scalar_tac)
  let weights : Array E 4#usize := ⟨values.val,values.property⟩
  refine ⟨weights,?_,?_⟩
  · exact builder_success 4#usize inst (low,powers) values finalState hcells
  · intro j hj
    rw [lookup_get weights field.wide_exact.WideExact.ZERO j (by simpa using hj)]
    simpa only [weights,V,show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hvalues j hj

/-- Complete original source helper, including both nested power-table
builders, all actual 16-cell loops, checked indices and the final four-cell
array construction. Arithmetic refinement is supplied by a concrete instance,
not by an optimization-equivalence law. -/
theorem source_success (low : Low) (extra : Extra)
    (hlow : ∀ s, s<16 → A.canonicalE (lookup low field.wide_exact.WideExact.ZERO s))
    (hextra : ∀ side, side<2 → A.canonicalK (lookup extra field.QM31.ONE side)) :
    ∃ weights : Array E 4#usize, old.twofold_libra_weights low extra=.ok weights ∧
      ∀ j, j<4 → A.canonicalE (lookup weights field.wide_exact.WideExact.ZERO j) ∧
        A.decodeE (lookup weights field.wide_exact.WideExact.ZERO j)=block A low extra j := by
  obtain ⟨powers,hpowers,hvalid⟩ := CuSavingsLibraReferencePowers.source_success A extra hextra
  obtain ⟨weights,hweights,hvalues⟩ := array_success A low powers extra hlow hvalid
  refine ⟨weights,?_,hvalues⟩
  unfold old.twofold_libra_weights
  rw [hpowers]
  simpa only [bind_tc_ok] using hweights

#print axioms array_success
#print axioms source_success
end AspisR1.CuSavingsLibraReference
