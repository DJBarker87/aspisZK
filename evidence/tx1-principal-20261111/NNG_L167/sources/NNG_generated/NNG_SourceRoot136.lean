import NNG_TreeSuffixes
import NNG_ProjectionLaws136
import NNG_Canonical136
import NNG_Observed136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceRoot136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_Projection136 NNG_Observed136

def value {VL : RSL.VLib} {H W : Type} (p : Representation VL H) (s : Parent H W)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state root : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H) : RSL.Verified VL :=
  ⟨(VL.c1Root (p.prefixValue s.prefixValue),p.b32 root),p.challenges s.challenges,
    p.alpha alpha,p.claims claims,p.k29 extra,p.k29 before,p.b32 state,
    (p.point z0,p.point z1),p.transcript t3⟩

theorem panic_env {E A : Type} (env : RSL.Env) :
    (RSL.RE.lift RSL.Spec.panic : RSL.RE E A) env ⟨.abort,[]⟩ := by
  unfold RSL.RE.lift RSL.Spec.map
  exact Or.inr (Or.inl ⟨[],rfl,rfl⟩)
#print axioms panic_env

/-- Actual unwrap and final constructor, all TryFrom Result arms. -/
theorem a3 {VL : RSL.VLib} {H W : Type} (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H)
    (r11 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
    (match r11 with
      | .Ok root => RSL.RE.pure (value p s alpha claims extra before state root z0 z1 t3)
      | .Err _ => RSL.RE.lift RSL.Spec.panic) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_a3 c s alpha claims extra state z0 before t3 z1 r11)) := by
  cases r11 with
  | Ok root =>
    change (⟨.ret (.ok (verified p
      (⟨Array.make 2#usize [s.prefixValue.c1_root,root],s.challenges,alpha,claims,
        extra,before,state,Array.make 2#usize [z0,z1],t3⟩ : r1_semantic.Verified H))),[]⟩ :
      RSL.Obs (Except VL.WErr (RSL.Verified VL))) =
      ⟨.ret (.ok (value p s alpha claims extra before state root z0 z1 t3)),[]⟩
    rw [verified_constructor]
    rfl
  | Err err =>
    change (RSL.RE.lift RSL.Spec.panic : RSL.RE VL.WErr (RSL.Verified VL)) env ⟨.abort,[]⟩
    exact panic_env env
#print axioms a3

/-- Complete source copy/unwrap suffix against the canonical Ref suffix.
Both length arms are preserved; no payload-length premise is added to 136. -/
theorem root32 {VL : RSL.VLib} {H W : Type} (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H) (bytes : Slice U8) :
    NNG_Canonical136.root32 VL (args p s) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) (p.bytes bytes) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_r11 c s alpha claims extra state z0 before t3 z1 bytes)) := by
  by_cases len : bytes.val.length = 32
  · have hs : bytes.length = (32#usize).val := len
    have converted : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes =
        .ok (.Ok (NNG_Root32.value bytes len)) := by
      unfold core.array.TryFromArrayCopySlice.try_from
      rw [dif_pos hs]
      rfl
    unfold NNG_Canonical136.root32
    rw [NNG_Projection136.root_some p bytes len]
    unfold NNG_TreeSuffixes.f_r11
    rw [converted]
    exact a3 p c s events env alpha claims extra before state z0 z1 t3 (.Ok (NNG_Root32.value bytes len))
  · have hs : bytes.length ≠ (32#usize).val := len
    have converted : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes =
        .ok (.Err ()) := by
      unfold core.array.TryFromArrayCopySlice.try_from
      rw [dif_neg hs]
    unfold NNG_Canonical136.root32
    rw [NNG_Projection136.root_none p bytes len]
    unfold NNG_TreeSuffixes.f_r11
    rw [converted]
    exact a3 p c s events env alpha claims extra before state z0 z1 t3 (.Err ())
#print axioms root32
end AspisR1.NNG_SourceRoot136
