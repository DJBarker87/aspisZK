import R1Z.ProverRwP6PowersNativeFactor
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersNativeCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverRwP6PowersNativeFactor ProverRwP6PowersFinite
variable [ExternalTypes]

theorem mapped (ops : ExternalFuns) (N : Usize) (x : W) (left : U8) (hl : left.val=N.val) :
    ProverRwP6ResultMap.map nativeArray (ProverRwP6PowersInstall.powers ops N x) =
      AspisR1ProducerRelease47.power_fill
        (Array.repeat N AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)
        (toW x) AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE 0#usize left := by
  letI : ExternalFuns := dict ops
  have step := ProverRwP6PowersNativeBridge.transport ops x N.val
    (Array.repeat N zero) one 0#usize left (by change 0+_= _; omega) hl
  simp only [nativeArray,ProverRwP6ArrayMap.repeat_map,zero,one,
    ProverRwDictionaryTower.native_w_roundtrip] at step
  calc
    _ = ProverRwP6ResultMap.map nativeArray
        (ProverRwP6ResultMap.map finish (finite x N.val (Array.repeat N zero) one 0#usize)) :=
      congrArg (ProverRwP6ResultMap.map nativeArray) (factor ops N x)
    _ = _ := ProverRwP6ResultMap.compose finish nativeArray _
    _ = _ := step

theorem exact_result (ops : ExternalFuns) (N : Usize) (x : W) (left : U8) (hl : left.val=N.val) :
    ProverRwP6PowersInstall.powers ops N x =
      ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)
        (AspisR1ProducerRelease47.power_fill
          (Array.repeat N AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)
          (toW x) AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE 0#usize left) := by
  have undo := ProverRwP6ResultMap.roundtrip nativeArray (ProverRwP6ArrayMap.map fromW)
    (fun out => ProverRwP6ArrayMap.roundtrip toW fromW ProverRwDictionaryTower.w_roundtrip out)
    (ProverRwP6PowersInstall.powers ops N x)
  exact undo.symm.trans (congrArg (ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW))
    (mapped ops N x left hl))
#print axioms mapped
#print axioms exact_result
end R1Z.ProverRwP6PowersNativeCaller
