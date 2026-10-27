import FJc_Constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InstalledParts
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
/-- Constructor operands projected into the native Pair's own weight carrier. -/
theorem value (v : transport.Variant) (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w)) :
    ∃ points a8 a9 factors1 factors2,
      FIn_WeightsExtract.state_only_prefix.r0.statement_points
        (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)=ok points ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) 8#usize=ok a8 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) 9#usize=ok a9 ∧
      FIn_WeightsExtract.weights_new_loop0 {start:=0#usize,«end»:=3#usize} points
        (Array.repeat 5#usize (Array.repeat 5#usize
          (Array.repeat 4#usize FIn_WeightsExtract.field.QM31.ZERO)))=ok factors1 ∧
      FIn_WeightsExtract.weights_new_loop1 {start:=0#usize,«end»:=2#usize}
        (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) factors1=ok factors2 ∧
      (FIo_Install.toWeights w).variant=FIo_Install.variant (FIn_WeightsInstall.variant v) ∧
      (FIo_Install.toWeights w).points=FIn_WeightsInstall.mapArray
        (FIn_WeightsInstall.mapArray FIo_Install.toQ) points ∧
      (FIo_Install.toWeights w).extra=FIn_WeightsInstall.mapArray FIo_Install.toQ
        (Array.make 2#usize [a8,a9]) ∧
      (FIo_Install.toWeights w).factors=FIn_WeightsInstall.mapArray
        (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) factors2 := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,same⟩ :=
    FJc_Constructor.parts _ _ _ w (FJc_Constructor.source v alpha z w run)
  subst w
  exact ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,rfl,rfl,rfl,rfl⟩
#print axioms value
end AspisR1.FJc_InstalledParts
end
