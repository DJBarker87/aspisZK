import R1Z.PV_RunJoin_NativePowerLoop66
import R1Z.ProverRwP6PowersGammaSource
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerBinding66
open Aeneas Aeneas.Std Result
open PV_RunJoin_NativePowerCarrier66 PV_RunJoin_NativePowerArray66
open PV_RunJoin_WeightMap46 (mapResult)
open PV_B2_F_ConstructorCarrier (amap)

theorem zero : toS PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO=
    AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO := rfl
theorem one : toS PV_B1_254.aspis_core.field.wide_exact.WideExact.ONE=
    AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE := rfl

theorem mapped (N : Usize) (x : W) (left : U8) (hl : left.val=N.val) :
    mapResult image (PV_B1_254.powers N x)=
      AspisR1ProducerRelease47.power_fill
        (Array.repeat N AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)
        (toS x) AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE 0#usize left := by
  rw [PV_B1_PowersControl.op254_source]
  have h := PV_RunJoin_NativePowerLoop66.complete x N.val
    (Array.repeat N PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO)
    PV_B1_254.aspis_core.field.wide_exact.WideExact.ONE 0#usize left (by change 0+_= _;omega) hl
  have repeat : image (Array.repeat N PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO)=
      Array.repeat N AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO := by
    change ProverRwP6ArrayMap.map toS (Array.repeat N _)=_
    rw [ProverRwP6ArrayMap.repeat_map,zero]
  rw [repeat,one] at h
  exact h

theorem undo (x : W) : ProverRwDictionaryTower.fromW (toS x)=PV_B1_ActualCarrierWide.fromW x := by
  rw [PV_RunJoin_NativePowerCarrier66.source,ProverRwDictionaryTower.w_roundtrip]

theorem decode {N : Usize} (r : Result (Array W N)) :
    mapResult (amap ProverRwDictionaryTower.fromW) (mapResult image r)=
      mapResult (amap PV_B1_ActualCarrierWide.fromW) r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok out =>
    apply congrArg Result.ok
    apply Subtype.ext
    change (out.val.map toS).map ProverRwDictionaryTower.fromW=out.val.map PV_B1_ActualCarrierWide.fromW
    rw [List.map_map]
    have h : ProverRwDictionaryTower.fromW ∘ toS=PV_B1_ActualCarrierWide.fromW := funext undo
    rw [h]

theorem gamma (x : ProverRwFull.aspis_core.field.wide_exact.WideExact) :
    PV_B1_ActualInstall.powers 29#usize x=
      mapResult (amap ProverRwDictionaryTower.fromW)
        (AspisR1ProducerRelease47.gamma (ProverRwDictionaryTower.toW x)) := by
  change mapResult (amap PV_B1_ActualCarrierWide.fromW)
    (PV_B1_254.powers 29#usize (PV_B1_ActualCarrierWide.toW x))=_
  rw [←decode,mapped 29#usize _ 29#u8 (by decide)]
  rw [PV_RunJoin_NativePowerCarrier66.source,PV_B1_ActualCarrierWide.from_to]
  rfl
#print axioms zero
#print axioms one
#print axioms mapped
#print axioms undo
#print axioms decode
#print axioms gamma
end R1Z.PV_RunJoin_NativePowerBinding66
