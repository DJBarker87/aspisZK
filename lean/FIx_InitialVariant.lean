import FIx_Absorption
import FIw_CoefficientTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_InitialVariant
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
abbrev Variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant

theorem value (v : Variant) (a b c : NQ) (out : NQ × NQ × NQ × NQ)
    (ha : Canon a) (hb : Canon b) (hc : Canon c)
    (run : pool_v1.pair_forest_semantic_terminal.initial_variant_selectors v a b c=ok out) :
    Canon out.1 ∧ Canon out.2.1 ∧ Canon out.2.2.1 ∧ Canon out.2.2.2 ∧
      (decode out.1,decode out.2.1,decode out.2.2.1,decode out.2.2.2)=
      R0P.scheduleVariantSelectors (FIw_CoefficientTransport.variant v) (decode a) (decode b) (decode c) := by
  cases v with
  | PrivateTransfer =>
    unfold pool_v1.pair_forest_semantic_terminal.initial_variant_selectors at run
    obtain ⟨sum,hs,run⟩ := FIv_Map.bind_success _ _ _ run
    cases Result.ok.inj run
    have vs := FIv_NativeValue.add a b sum ha hb hs
    exact ⟨ha,FIv_NativeValue.zero.1,vs.1,hc,by
      simp only [R0P.scheduleVariantSelectors,FIw_CoefficientTransport.variant,
        FIv_NativeValue.zero.2,vs.2]⟩
  | Withdrawal =>
    unfold pool_v1.pair_forest_semantic_terminal.initial_variant_selectors at run
    obtain ⟨sum,hs,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨sum1,hs1,run⟩ := FIv_Map.bind_success _ _ _ run
    cases Result.ok.inj run
    have vs := FIv_NativeValue.add a b sum ha hb hs
    have vs1 := FIv_NativeValue.add sum c sum1 vs.1 hc hs1
    exact ⟨FIv_NativeValue.zero.1,vs1.1,FIv_NativeValue.zero.1,FIv_NativeValue.zero.1,by
      simp only [R0P.scheduleVariantSelectors,FIw_CoefficientTransport.variant,
        FIv_NativeValue.zero.2,vs1.2,vs.2]⟩
#print axioms value
end AspisR1.FIx_InitialVariant
end
