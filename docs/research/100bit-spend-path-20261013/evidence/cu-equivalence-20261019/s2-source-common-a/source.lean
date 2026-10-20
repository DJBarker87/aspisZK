import AspisR1S2Groups.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceCommon
open Aeneas Aeneas.Std Result AspisR1S2Groups
variable [Shared]

theorem field_eq (bytes : Slice U8) (j : Usize) : new.field bytes j = old.field bytes j := by rfl

theorem variant_eq (v : transport.Variant) :
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq v transport.Variant.S2 =
      .ok (decide (v = transport.Variant.S2)) := by
  cases v <;> simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,read_discriminant]

theorem size_product : (64#usize * 32#usize : Result Usize) = .ok 2048#usize := by
  obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=64#usize) (y:=32#usize) (by scalar_tac))
  have he : x=2048#usize := UScalar.eq_of_val_eq (by scalar_tac)
  simpa only [he] using hx

theorem fallback0 (w : Weights) (iter : core.ops.range.Range Usize) (f : Slice U8)
    (m : Array U16 64#usize) (c : Array field.wide_exact.WideExact 64#usize) (n : Usize) :
    new.grouped_inactive_pair_loop0 iter w.variant w.factors w.points w.extra f m c n =
      old.grouped_inactive_pair_loop0 iter w f m c n := by rfl

theorem fallback2 (w : Weights) (iter : core.ops.range.Range Usize) (f : Slice U8)
    (m : Array U16 64#usize) (c : Array field.wide_exact.WideExact 64#usize) (n : Usize) :
    new.grouped_inactive_pair_loop2 iter w.variant w.factors w.points w.extra f m c n =
      old.grouped_inactive_pair_loop0 iter w f m c n := by rfl

theorem fallback1 (iter : core.ops.range.Range Usize) (low : Array field.wide_exact.WideExact 16#usize)
    (m : Array U16 64#usize) (c : Array field.wide_exact.WideExact 64#usize) (pair : field.wide_exact.WideExact) :
    new.grouped_inactive_pair_loop1 iter low m c pair =
      old.grouped_inactive_pair_loop1 iter low m c pair := by rfl

theorem fallback3 (iter : core.ops.range.Range Usize) (low : Array field.wide_exact.WideExact 16#usize)
    (m : Array U16 64#usize) (c : Array field.wide_exact.WideExact 64#usize) (pair : field.wide_exact.WideExact) :
    new.grouped_inactive_pair_loop3 iter low m c pair =
      old.grouped_inactive_pair_loop1 iter low m c pair := by rfl

#print axioms field_eq
#print axioms variant_eq
#print axioms size_product
#print axioms fallback0
#print axioms fallback2
#print axioms fallback1
#print axioms fallback3
end AspisR1.CuSavingsS2SourceCommon
