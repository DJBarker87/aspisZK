import AspisR1CanonicalInputs.Funs
import CuSavingsArrayFromFn
import CuSavingsLibraSourceBuilder
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalInputPowers
open Aeneas Aeneas.Std Result AspisR1CanonicalInputs
abbrev E := field.wide_exact.WideExact
abbrev Canonical (x : E) : Prop := CuSavingsWideArithmetic.CanonicalE (toE x)
def decode (x : E) : CuSavingsWideArithmetic.ExactE := CuSavingsWideArithmetic.decodeE (toE x)

theorem to_from (x : CoreE) : toE (fromE x)=x := rfl

theorem mul (x y : E) (hx : Canonical x) (hy : Canonical y) :
    ∃ z,field.wide_exact.WideExact.mul x y=.ok z ∧ Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hc,hv⟩ := CuSavingsWideArithmetic.mul (toE x) (toE y) hx hy
  refine ⟨fromE z,?_,?_,?_⟩
  · simp only [field.wide_exact.WideExact.mul,hz,bind_tc_ok]
  · change CuSavingsWideArithmetic.CanonicalE (toE (fromE z))
    rw [to_from]
    exact hc
  · simpa only [decode,to_from] using hv

def powerRaw (power base : E) : Result (E × (E × E) × ((E × E)→(E × E))) := do
  let product ← field.wide_exact.WideExact.mul power base
  .ok (power,(product,base),fun c=>(c.1,base))

theorem callback_handback {N : Usize} (power base : E) (i : Usize) :
    weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      (N:=N) (power,base) i =
      (do let (value,updated,back) ← powerRaw power base
          .ok (value,back updated)) := by
  change (do let (value,updated,back) ← powerRaw power base
             .ok (value,(back updated).1,base)) = _
  unfold powerRaw
  cases h : field.wide_exact.WideExact.mul power base <;>
    simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div] <;> rfl

theorem callback {N : Usize} (power base : E) (i : Usize) :
    (weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact N).call_mut (power,base) i =
      (do let product ← field.wide_exact.WideExact.mul power base
          .ok (power,(product,base))) := by
  change weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once (power,base) i = _
  rw [callback_handback]
  unfold powerRaw
  cases h : field.wide_exact.WideExact.mul power base <;>
    simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div] <;> rfl

theorem one_canonical : Canonical field.wide_exact.WideExact.ONE := by
  simp [Canonical,toE,toK,CuSavingsWideArithmetic.CanonicalE,CuSavingsWideArithmetic.CanonicalK,
    ExtractedCurrentTowerAdd.CanonicalQM,ExtractedCurrentTowerAdd.CanonicalCM,
    ExtractedCurrentTowerAdd.P,ExtractedCurrentM31AddSub.P,
    field.wide_exact.WideExact.ONE,field.QM31.ONE,field.QM31.ZERO,
    AspisR1WideArithmetic.toK,AspisR1WideArithmetic.toC]

theorem one_value : decode field.wide_exact.WideExact.ONE=1 := by
  ext <;> simp [decode,toE,toK,CuSavingsWideArithmetic.decodeE,CuSavingsWideArithmetic.decodeK,
    ExtractedCurrentQM31Exact.decode,field.wide_exact.WideExact.ONE,field.QM31.ONE,field.QM31.ZERO,
    AspisR1WideArithmetic.toK,AspisR1WideArithmetic.toC,
    QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

theorem source_success (N : Usize) (q : E) (hq : Canonical q)
 :
    ∃ powers, weights.powers N q=.ok powers ∧
      ∀ i (hi : i<N.val),
        Canonical (powers.val[i]'(by rw [powers.property];exact hi)) ∧
        decode (powers.val[i]'(by rw [powers.property];exact hi))=(decode q)^i := by
  have hN : N.val<Usize.size := by
    simp only [Usize.size,Usize.numBits,UScalarTy.numBits]
    exact N.bv.isLt
  let inst := weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact N
  let P : Nat → weights.powers.closure N → Prop := fun j state =>
    Canonical state.1 ∧ state.2=q ∧ decode state.1=(decode q)^j
  let V : Nat → E → Prop := fun j value => Canonical value ∧ decode value=(decode q)^j
  have hstep : ∀ j state index, j<N.val → index.val=j → P j state →
      ∃ value state1, inst.call_mut state index=.ok (value,state1) ∧ V j value ∧ P (j+1) state1 := by
    intro j state index _ _ hp
    rcases state with ⟨power,base⟩
    rcases hp with ⟨hpower,hbase,hvalue⟩
    change base=q at hbase
    change Canonical power at hpower
    change decode power=(decode q)^j at hvalue
    subst base
    obtain ⟨product,hproduct,hcanonical,hdecode⟩ := mul power q hpower hq
    refine ⟨power,(product,q),?_,⟨hpower,hvalue⟩,hcanonical,rfl,?_⟩
    · change (weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact N).call_mut
        (power,q) index=.ok (power,(product,q))
      rw [callback,hproduct]
      rfl
    · simpa only [hvalue,pow_succ] using hdecode
  have initial : P 0 (field.wide_exact.WideExact.ONE,q) := ⟨one_canonical,rfl,by simpa only [pow_zero] using one_value⟩
  obtain ⟨values,finalState,hcells,hvalues,_⟩ :=
    CuSavingsLibraSourceBuilder.cells_success inst P V N.val hstep N.val 0#usize
      (field.wide_exact.WideExact.ONE,q) initial (by simp) hN
  let powers : Array E N := ⟨values.val,values.property⟩
  refine ⟨powers,?_,?_⟩
  · unfold weights.powers AspisR1CanonicalInputs.core.array.from_fn_mut
    dsimp only [inst] at hcells
    rw [hcells]
    rfl
  · intro i hi
    simpa only [powers,V,show (0#usize).val=0 by scalar_tac,Nat.zero_add] using hvalues i hi

#print axioms source_success
#print axioms mul
#print axioms callback_handback
#print axioms callback
#print axioms one_canonical
#print axioms one_value
end AspisR1.CuSavingsCanonicalInputPowers
