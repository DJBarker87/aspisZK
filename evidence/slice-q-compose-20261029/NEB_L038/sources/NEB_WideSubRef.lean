import NEB_ArrayRefs
import NEB_WideSubCalls
set_option autoImplicit false
namespace NEB_WideSubRef
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs

def words (x : AspisR1CurrentWide.field.wide_exact.WideExact) : Array U32 8#usize :=
  Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
    x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem reference (x y : NE) (hx : canonE x) (hy : canonE y) :
    NEB_AdditiveRef.sub8 (wordsE x) (wordsE y) =
      (do let z ← AspisR1CurrentWide.field.wide_exact.WideExact.sub
            (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y)
          ok (words z)) := by
  simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub,
    AspisR1CurrentWide.field.QM31.sub,AspisR1CurrentWide.field.CM31.sub,
    NBG_GetterPorts.wide,NBG_GetterPorts.qm,bind_assoc_eq]
  rw [← NBG_CheckedSub.m31 x.c0.c0.a y.c0.c0.a hx.1.1.1 hy.1.1.1,
    ← NBG_CheckedSub.m31 x.c0.c0.b y.c0.c0.b hx.1.1.2 hy.1.1.2,
    ← NBG_CheckedSub.m31 x.c0.c1.a y.c0.c1.a hx.1.2.1 hy.1.2.1,
    ← NBG_CheckedSub.m31 x.c0.c1.b y.c0.c1.b hx.1.2.2 hy.1.2.2,
    ← NBG_CheckedSub.m31 x.c1.c0.a y.c1.c0.a hx.2.1.1 hy.2.1.1,
    ← NBG_CheckedSub.m31 x.c1.c0.b y.c1.c0.b hx.2.1.2 hy.2.1.2,
    ← NBG_CheckedSub.m31 x.c1.c1.a y.c1.c1.a hx.2.2.1 hy.2.2.1,
    ← NBG_CheckedSub.m31 x.c1.c1.b y.c1.c1.b hx.2.2.2 hy.2.2.2]
  simp [NEB_AdditiveRef.sub8,wordsE,words,Array.index_usize,Array.make,NEB_WordRefs.sub]

theorem result (x y : NE) (hx : canonE x) (hy : canonE y) : ∃ z : NE,
    AspisR1CurrentWide.field.wide_exact.WideExact.sub
      (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y)=ok (NBG_GetterPorts.wide z) ∧
    NEB_AdditiveRef.sub8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z := by
  obtain ⟨z,run,cz,_⟩ := NBG_CheckedSub.wide_result x y hx hy
  exact ⟨z,run,by rw [reference x y hx hy,run];rfl,cz⟩

#print axioms reference
#print axioms result
end NEB_WideSubRef
