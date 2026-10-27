import LPh_RawSpec
import RPu_FJf_RawArithmetic
set_option autoImplicit false
namespace AspisR1.LPh.Raw
open Aeneas Aeneas.Std Result
open FJf_RawReference JFs_TX2_RawMap

theorem size64 : UScalar.size .U64=18446744073709551616 := by
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]

theorem wrapping_sub_nat (x y : U64) :
    (U64.wrapping_sub x y).val=RawSpec.sub64 x.val y.val := by
  rw [U64.wrapping_sub_val_eq,size64]
  unfold RawSpec.sub64 RawSpec.wrap64
  change (x.val+(18446744073709551616-y.val))%18446744073709551616 =
    (x.val+18446744073709551616-y.val)%18446744073709551616
  have hy:=y.hSize
  rw [size64] at hy
  congr 1
  omega

theorem partial_nat (x : U64) :
    (FIo_ReduceBounds.fold x).val=RawSpec.foldWord x.val := by
  have hv : (FIo_ReduceBounds.fold x).val=x.val%2147483648+x.val/2147483648 := JFv_TX2_FoldValue.source x
  change _ = (x.val%2147483648+x.val/2147483648)%18446744073709551616
  have hs := (FIo_ReduceBounds.fold x).hSize
  rw [size64] at hs
  rw [←hv,Nat.mod_eq_of_lt hs]

theorem twice_nat (x : U64) :
    (U64.wrapping_mul 2#u64 x).val=(2*x.val)%18446744073709551616 := by
  rw [U64.wrapping_mul_val_eq,size64]
  rfl

theorem raw_nat (a b c d e f g h : U32) :
    ∃ z, FIo_Native.fast_pairing.canonical.Q.raw (pack a b c d) (pack e f g h)=ok z ∧
      z.val.map UScalar.val=RawSpec.rawNat a.val b.val c.val d.val e.val f.val g.val h.val := by
  refine ⟨pack (raw0 a b c d e f g h) (raw1 a b c d e f g h)
    (raw2 a b c d e f g h) (raw3 a b c d e f g h),FJf_RawReference.source a b c d e f g h,?_⟩
  change [(raw0 a b c d e f g h).val,(raw1 a b c d e f g h).val,
    (raw2 a b c d e f g h).val,(raw3 a b c d e f g h).val]=_
  simp only [raw0,raw1,raw2,raw3,u,v,add,sub,mul,
    U64.wrapping_add_val_eq,twice_nat,wrapping_sub_nat,partial_nat,
    FJf_RawArithmetic.product_value,RawSpec.rawNat,RawSpec.sub64,RawSpec.wrap64,
    size64,
    show (4611686014132420609#u64).val=4611686014132420609 from rfl,
    show (6442450941#u64).val=6442450941 from rfl,
    show (9223372028264841218#u64).val=9223372028264841218 from rfl,
    Nat.add_mod,Nat.mod_mod]

#print axioms size64
#print axioms twice_nat
#print axioms wrapping_sub_nat
#print axioms partial_nat
#print axioms raw_nat
end AspisR1.LPh.Raw
