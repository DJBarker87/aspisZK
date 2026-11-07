import NNG_ProjectionFallback137
import LIB_VDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Data137
open Aeneas Aeneas.Std Result
abbrev VL := LIB_VLib.library
abbrev Args := RSL.TX1_137.Args VL

/-- A total byte representative; the own byte-domain proves its live branch. -/
def bytes (b : RSL.Bytes) : Slice U8 := by
  classical
  exact if h : b.length≤Usize.max then LIB_Bytes.fromBytes b h else ⟨[],by exact Nat.zero_le _⟩

theorem byte_bound (a : Args) (domain : RSL.TX1_137.Domain VL a) : a.bytes.length≤Usize.max := by
  have small := (57607#usize).hmax
  have bound : a.bytes.length≤57607 := domain.2
  scalar_tac
#print axioms byte_bound

theorem bytes_exact (a : Args) (domain : RSL.TX1_137.Domain VL a) : LIB_Carriers.bytes (bytes a.bytes) = a.bytes := by
  unfold bytes
  rw [dif_pos (byte_bound a domain)]
  exact LIB_Bytes.bytes_from _ _
#print axioms bytes_exact

/-- Chosen only from deterministic CLOSED staged evaluators, never a native
cut image or an assumed successful parent result. Stops use a fixed zero. -/
def fallback (a : Args) (env : RSL.Env) : LIB_VCarriers.QM31 :=
  match LIB_VParsePrefix.eval a.bytes with
  | .error _ => NNG_ProjectionFallback137.zero
  | .ok p => match LIB_VPublicTranscript.eval (a.public_,LIB_VCarriers.c1Root p) env with
    | .error _ => NNG_ProjectionFallback137.zero
    | .ok initial => match LIB_VBegin.eval (p,initial) env with
      | .error _ => NNG_ProjectionFallback137.zero
      | .ok (c,_) => c.eta
end AspisR1.NNG_Data137
