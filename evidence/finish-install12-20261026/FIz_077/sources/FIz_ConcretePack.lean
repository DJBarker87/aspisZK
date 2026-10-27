import FIz_PackLinear
import R1ConcretePackBasis
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ConcretePack
open FIv_NativeValue (K)
def embed : K →+* AspisWideTower.WideExact := algebraMap K AspisWideTower.WideExact
/-- Explicit field transport; native coefficients live in QM31Exact, whereas
ConcretePackBasis belongs to WideExact. No carrier equality is asserted. -/
theorem value (a : Fin 4 → K) : embed (FIx_PreweightedPack.pack a)=
    R0P.pack4 ConcretePackBasis.basis (fun j=>embed (a j)) := by
  unfold FIx_PreweightedPack.pack R0P.pack4
  simp only [map_add,map_mul]
  have hi : embed ExtractedMaskQmPackBase4Arithmetic.iBasis=ConcretePackBasis.iE := by
    rfl
  have hu : embed ExtractedMaskQmPackBase4Arithmetic.uBasis=ConcretePackBasis.uE := by
    rfl
  rw [hi,hu]
  rfl
#print axioms value
end AspisR1.FIz_ConcretePack
end
