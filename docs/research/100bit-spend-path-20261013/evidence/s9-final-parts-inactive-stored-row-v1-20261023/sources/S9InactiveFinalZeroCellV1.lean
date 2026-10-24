import S9ActiveFourFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9InactiveFinalZeroCellV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9FactorArrayEntryV1
open AspisR1S9ActiveFourFrameV1 (W Parts Libra R)

def cell0 (parts : Parts) : W := atN parts 0#usize (by decide)

theorem cell0_read (parts : Parts) : Array.index_usize parts 0#usize=.ok (cell0 parts) :=
  index_atN parts 0#usize (by decide)

theorem write_active_cell0 (f : Slice U8) (libra : Libra) (iter : R)
    (initial middle final : Parts) (inactive : W)
    (hwrite : Array.update initial 0#usize inactive=.ok middle)
    (hactive : weights.Weights.pair_loop8 iter f middle libra=.ok final) : cell0 final=inactive := by
  have hf := AspisR1S9ActiveFourFrameV1.active_success_frame f libra iter middle final hactive
    0#usize (by decide) (by decide)
  have hu := accepted_update_eq_set initial 0#usize (by decide) inactive middle hwrite
  unfold cell0
  rw [hf,hu,atN_set initial 0#usize 0#usize inactive (by decide) (by decide)] <;> rfl

theorem write_unshared_active_cell0 (f : Slice U8) (libra : Libra) (iter : R)
    (initial middle final : Parts) (inactive : W)
    (hwrite : Array.update initial 0#usize inactive=.ok middle)
    (hactive : weights.Weights.pair_loop16 iter f middle libra=.ok final) : cell0 final=inactive := by
  rw [AspisR1S9ActiveFourCanonicalV1.unshared_active_eq] at hactive
  exact write_active_cell0 f libra iter initial middle final inactive hwrite hactive

/-- Exact textual reuse of the lead's already-green span product proof. -/
theorem final_span_wrapping_product : Usize.wrapping_mul 64#usize 32#usize=2048#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_mul_val_eq]
  change 2048 % UScalar.size .Usize = 2048
  have hv : (2048#usize).val=2048 := rfl
  exact Nat.mod_eq_of_lt (by simpa only [UScalar.size,hv] using (2048#usize).hBounds)

/-- Exact actual dispatch span implies the native byte-window bound; this
is not inferred from Pair's floor(length/32)=64. -/
theorem exact_span_bytes_bound (f : Slice U8)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize) : 2048≤f.val.length := by
  have hs := hspan
  rw [final_span_wrapping_product] at hs
  have hv := congrArg (fun x : Usize=>x.val) hs
  change f.val.length=2048 at hv
  omega

theorem exact_s2_dispatch_helper (self : weights.Weights) (f : Slice U8)
    (low : Array W 16#usize) (out : W) (hs2 : self.variant=transport.Variant.S2)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (h : weights.grouped_inactive_pair self f low=.ok out) :
    weights.s2_grouped_inactive_pair f low=.ok out := by
  have hv : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.S2=.ok true := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  unfold weights.grouped_inactive_pair at h
  rw [hv] at h
  simp only [bind_tc_ok,lift,hspan,↓reduceIte] at h
  exact h

#print axioms cell0_read
#print axioms write_active_cell0
#print axioms write_unshared_active_cell0
#print axioms final_span_wrapping_product
#print axioms exact_span_bytes_bound
#print axioms exact_s2_dispatch_helper
end AspisR1S9InactiveFinalZeroCellV1
