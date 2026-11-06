import NIW_AlignHighPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPartialPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

structure Log where
 high : Option (Result (RU×Parts))
 tail : Option (Option NIW_AlignTailPhase.Log)

def run (c : Context) (w : Ref W) (parts : Parts) (reply : RP) : Result NR × Log :=
 match reply with
 | .Err err => (ok (.Err err),⟨none,none⟩)
 | .Ok values =>
  let high := FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts
  match high with
  | fail err => (fail err,⟨some high,none⟩)
  | div => (div,⟨some high,none⟩)
  | ok (returned,after) =>
   let tail := NIW_AlignHighPhase.run c w after returned
   (tail.1,⟨some high,some tail.2⟩)

theorem trace (c : Context) (w : Ref W) (parts : Parts) (reply : RP)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (hf : NHI_TensorOuterStep.Factors w.value) (ce : NHI_CellCanon.array w.value.extra)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) (ck : canonE c.kappa) :
 NIT_SharedChain.Partial c w parts reply (run c w parts reply).1 := by
 cases reply with
 | Err err => exact .rejected err
 | Ok values =>
  cases high : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts with
  | fail err =>
   simp only [run,high]
   exact .failed values err high
  | div =>
   simp only [run,high]
   exact .diverged values high
  | ok result =>
   rcases result with ⟨returned,after⟩
   have post := NIG_PairFrames.high values w.value c.ap0.value c.ap1.value parts after hf c0 c1 cp returned high
   simp only [run,high]
   exact .returned values returned after _ high (NIW_AlignHighPhase.trace c w after returned s2 size c0 c1 ce post.1 ck)

#print axioms trace
end AspisR1.NIW_AlignPartialPhase
