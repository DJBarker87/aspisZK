import NDD_Simple
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_Composite
def cmArray (x : AspisR72Sampler.field.CM31) : Array U32 2#usize :=
  Array.make 2#usize [x.a,x.b]
def qmArray (x : AspisR72Sampler.field.QM31) : Array U32 4#usize :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]

theorem cm31_neg (x : AspisR72Sampler.field.CM31) :
    NDD_Reference.cm31_neg_ref (cmArray x) = (do
      let c ← AspisR72Sampler.field.CM31.neg x
      ok (cmArray c)) := by
  simp [NDD_Reference.cm31_neg_ref, cmArray,
    AspisR72Sampler.field.CM31.neg, ← NDD_Simple.m31_neg]

theorem qm31_zero (x : AspisR72Sampler.field.QM31) :
    NDD_Reference.qm31_zero_ref (qmArray x) =
      AspisR72Sampler.field.QM31.is_zero x := by
  simp [NDD_Reference.qm31_zero_ref,qmArray,
    AspisR72Sampler.field.QM31.is_zero,AspisR72Sampler.field.CM31.is_zero,
    AspisR72Sampler.field.M31.is_zero]
#print axioms cm31_neg
#print axioms qm31_zero
end NDD_Composite
