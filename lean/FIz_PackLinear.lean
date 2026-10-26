import FIx_PreweightedPack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_PackLinear
open FIv_NativeValue (K)
theorem add (a b : Fin 4 → K) :
    FIx_PreweightedPack.pack (fun i=>a i+b i)=FIx_PreweightedPack.pack a+FIx_PreweightedPack.pack b := by
  unfold FIx_PreweightedPack.pack
  ring

theorem zero : FIx_PreweightedPack.pack (fun _=>0)=0 := by
  simp only [FIx_PreweightedPack.pack,mul_zero,add_zero]
#print axioms add
#print axioms zero
end AspisR1.FIz_PackLinear
end
