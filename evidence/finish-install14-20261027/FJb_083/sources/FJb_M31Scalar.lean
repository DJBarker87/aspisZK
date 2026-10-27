import FJa_PoseidonPow5
import ExtractedMaskM31AddSub
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_M31Scalar
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm cm)
open FIv_NativeValue (K Canon decode)
abbrev P := ExtractedMaskM31AddSub.P
def updated (x : NQ) (m : U32) : NQ := {x with c0 := {x.c0 with a := m}}
def source (x : NQ) (c : U32) : Result NQ := do
  let m ← field.M31.add x.c0.a c
  state_only_poseidon.pow5 (updated x m)
/-- The installed M31-constant S-box cell, on its actual canonical operands. -/
theorem value (x out : NQ) (c : U32) (hx : Canon x) (hc : c.val < P)
    (run : source x c=ok out) : Canon out ∧ decode out=(decode x+(c.val : K))^5 := by
  unfold source at run
  obtain ⟨m,hm,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨m',hm',hv,hcanon⟩ := ExtractedMaskM31AddSub.current_add_mod x.c0.a c hx.1.1 hc
  have hnative := (FIv_NativeArithmetic.m31_add x.c0.a c).trans hm'
  have he : m=m' := Result.ok.inj (hm.symm.trans hnative)
  subst m'
  have hu : Canon (updated x m) := ⟨⟨hcanon,hx.1.2⟩,hx.2⟩
  have hd : decode (updated x m)=decode x+(c.val : K) := by
    ext <;> simp [decode,ExtractedMaskQM31Exact.decode,qm,cm,updated,hv,
      P,ExtractedMaskM31AddSub.P,AspisV8R15.ExactTowerBase.P,ZMod.natCast_mod]
  have vo := FJa_PoseidonPow5.value (updated x m) out hu run
  exact ⟨vo.1,vo.2.trans (congrArg (fun z : K=>z^5) hd)⟩
#print axioms value
end AspisR1.FJb_M31Scalar
end
