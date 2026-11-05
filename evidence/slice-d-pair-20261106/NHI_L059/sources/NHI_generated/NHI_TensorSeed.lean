import NHI_TensorTotal
import NHI_FactoredProducers
set_option autoImplicit false
namespace NHI_TensorSeed
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem source (w : FIo_Native.weights.Weights) (k : Usize) (hk : k.val<5)
 (hf : NHI_TensorTotal.Factors w) (input : Slice NQ) (len : input.val.length=64)
 (ca : NHI_CellCanon.slice input) :
 ∃ out,FIo_Native.weights.Weights.tensor w k 2#usize input=ok out ∧
 NHI_CellCanon.slice out ∧ out.val.length=64 := by
 let seeded := NHI_SliceCells.put input 0 FIo_Native.aspis_core.field.QM31.ONE
 have update := NHI_SliceCells.update input 0#usize (by change 0<input.val.length;omega)
  FIo_Native.aspis_core.field.QM31.ONE
 have canonical : NHI_CellCanon.slice seeded :=
  NHI_CellCanon.put input 0 _ ca NHI_FactoredProducers.one_canonical
 have size : seeded.val.length=64 := (NHI_SliceCells.length input 0 _).trans len
 obtain ⟨out,run,co,lo⟩ := NHI_TensorTotal.outer w k hk hf seeded size canonical
 refine ⟨out,?_,co,lo⟩
 unfold FIo_Native.weights.Weights.tensor
 rw [update,bind_tc_ok]
 exact run

#print axioms source
end NHI_TensorSeed
