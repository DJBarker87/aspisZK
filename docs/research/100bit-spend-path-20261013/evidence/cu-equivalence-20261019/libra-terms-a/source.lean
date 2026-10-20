import CuSavingsLibraSourceScalar
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceTerms
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)
abbrev Points := Array E 4#usize
abbrev Powers := Array K 4#usize

theorem perm_eq : new.PERM=PERM := by unfold new.PERM PERM;rfl
theorem quarter_eq : new.QUARTER=QUARTER := by unfold new.QUARTER QUARTER;rfl

def term (p : Points) (high : Powers) (j : Nat) : R :=
  A.decodeE (lookup p field.wide_exact.WideExact.ZERO (CuSavingsLibraSourcePerm.perm j)) *
    A.embedding (A.decodeK (lookup high field.QM31.ONE j)) * A.quarter

theorem source_success (p : Points) (high : Powers)
    (hp : ∀ j, j<4 → A.canonicalE (lookup p field.wide_exact.WideExact.ZERO j))
    (hh : ∀ j, j<4 → A.canonicalK (lookup high field.QM31.ONE j)) :
    ∃ terms,
      AspisR1Libra.core.array.from_fn 4#usize
        new.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (p,high)=.ok terms ∧
      ∀ j (hj : j<4), A.canonicalE (lookup terms field.wide_exact.WideExact.ZERO j) ∧
        A.decodeE (lookup terms field.wide_exact.WideExact.ZERO j)=term A p high j := by
  let inst := new.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
  let C := new.factored_s2_libra_weights.closure
  let P : Nat → C → Prop := fun _ c => c=(p,high)
  let V : Nat → E → Prop := fun j value => A.canonicalE value ∧ A.decodeE value=term A p high j
  have step : ∀ j c index, j<4 → index.val=j → P j c →
      ∃ value c1, inst.call_mut c index=.ok (value,c1) ∧ V j value ∧ P (j+1) c1 := by
    intro j c index hj hi hc
    change c=(p,high) at hc
    subst c
    have hib : index.val<4 := by omega
    obtain ⟨entry,hentry,heb,hev⟩ := CuSavingsLibraSourcePerm.source index hib
    have hrp := read p field.wide_exact.WideExact.ZERO entry (by scalar_tac)
    have hrh := read high field.QM31.ONE index (by scalar_tac)
    obtain ⟨product,hproduct,hproductC,hproductV⟩ := A.mixed
      (lookup p field.wide_exact.WideExact.ZERO entry.val)
      (lookup high field.QM31.ONE index.val) (hp entry.val heb) (hh index.val hib)
    obtain ⟨value,hvalue,hvalueC,hvalueV⟩ := A.scalar product hproductC
    refine ⟨value,(p,high),?_,hvalueC,?_,rfl⟩
    · change new.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut (p,high) index=.ok (value,(p,high))
      unfold new.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      simp only [uncurry_apply_pair,perm_eq,quarter_eq]
      change (do
        let entry ← Array.index_usize PERM index
        let point ← Array.index_usize p entry
        let scalar ← Array.index_usize high index
        let product ← field.wide_exact.WideExact.mul_qm31 point scalar
        let value ← field.wide_exact.WideExact.mul_m31 product QUARTER
        .ok (value,(p,high))) = _
      simp only [hentry,hrp,hrh,hproduct,hvalue,bind_tc_ok]
    · change A.decodeE value=term A p high j
      rw [hvalueV,hproductV,hev,hi]
      rfl
  obtain ⟨values,finalState,hcells,hvalues,_⟩ :=
    CuSavingsLibraSourceBuilder.cells_success inst P V 4 step 4 0#usize (p,high) rfl
      (by scalar_tac) (by scalar_tac)
  let terms : Array E 4#usize := ⟨values.val,by simpa using values.property⟩
  refine ⟨terms,?_,?_⟩
  · unfold AspisR1Libra.core.array.from_fn CuSavingsArrayBuilder.build
    dsimp only [inst] at hcells
    rw [hcells]
    rfl
  · intro j hj
    have hv := hvalues j hj
    have hlen : j<terms.val.length := by simpa only [terms.property,show (4#usize).val=4 by scalar_tac] using hj
    simpa only [V,show (0#usize).val=0 by scalar_tac,Nat.zero_add,
      lookup,List.getD_eq_getElem terms.val field.wide_exact.WideExact.ZERO hlen] using hv

#print axioms perm_eq
#print axioms quarter_eq
#print axioms source_success
end AspisR1.CuSavingsLibraSourceTerms
