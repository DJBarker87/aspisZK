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

#print axioms mul
#print axioms callback_handback
#print axioms callback
#print axioms one_canonical
#print axioms one_value
end AspisR1.CuSavingsCanonicalInputPowers
