import R1Z.ProverRwP6WideDecode
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersCoordinates
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverCommitWideOps48

theorem read (N : Usize) (ys : Nat → Raw) (i : Usize) (hi : i.val<N.val) :
    Array.index_usize (ProverRwP6PowersGammaValues.fieldArray N ys) i =
      ok (fromW (source (ys i.val))) :=
  (ProverRwP6ArrayMap.index fromW (ProverCommitMix48.sourceArray N ys) i).trans
    (congrArg (ProverRwP6ResultMap.map fromW) (ProverCommitMix48.index N ys i hi))

theorem gamma [ExternalTypes] (ops : ExternalFuns) (x : Raw) (hx : canonical x) :
    ∃ out, (ProverRwP6PowersInstall.selected ops).op254 29#usize (fromW (source x)) = ok out ∧
      ∀ i : Usize, i.val<29 → ∃ cell, Array.index_usize out i = ok cell ∧
        ProverRwP6WideDecode.canonical cell ∧ ProverRwP6WideDecode.decode cell = value x^i.val := by
  obtain ⟨ys,hy,hc,hv⟩ := ProverRwP6PowersGammaValues.gamma ops x hx
  refine ⟨_,hy,?_⟩
  intro i hi
  refine ⟨fromW (source (ys i.val)),read 29#usize ys i hi,
    ProverRwP6WideDecode.canonical_source _ (hc i.val hi),?_⟩
  exact (ProverRwP6WideDecode.value_source _).trans (hv i.val hi)
#print axioms read
#print axioms gamma
end R1Z.ProverRwP6PowersCoordinates
