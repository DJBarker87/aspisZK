import RPv_FIz_PackShape
import R1ConcretePackBasis
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ConcretePack
open FIv_NativeValue (K)
def embed : K →+* AspisWideTower.WideExact := algebraMap K AspisWideTower.WideExact
attribute [local irreducible] embed
/-- Explicit field transport; native coefficients live in QM31Exact, whereas
ConcretePackBasis belongs to WideExact. No carrier equality is asserted. -/
theorem value (a : Fin 4 → K) : embed (FIx_PreweightedPack.pack a)=
    R0P.pack4 ConcretePackBasis.basis (fun j=>embed (a j)) := by
  rw [FIz_PackShape.value]
  unfold R0P.pack4
  simp only [map_add,map_mul]
  have hi : embed ExtractedMaskQmPackBase4Arithmetic.iBasis=ConcretePackBasis.iE := by
    unfold embed
    rfl
  have hu : embed ExtractedMaskQmPackBase4Arithmetic.uBasis=ConcretePackBasis.uE := by
    unfold embed
    rfl
  have bi : ConcretePackBasis.basis.i=ConcretePackBasis.iE := rfl
  have bu : ConcretePackBasis.basis.u=ConcretePackBasis.uE := rfl
  rw [hi,hu,bi,bu]
#print axioms value
end AspisR1.FIz_ConcretePack
end
