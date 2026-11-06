import NHX_RegularFrame
import NIT_RegularChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegular
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

/-- CLOSED process_kind semantics at each source-ordered entered call. The
whole Result includes its Vec and all seven Parts cells; there is no seed
array identification and no successful-child restriction. -/
def child (w : W) (f : Slice U8) (ap0 ap1 : Powers) :
 Usize → Scratch → Parts → Result NHM_RegularKinds.Reply :=
 fun k s p => NHX_ProcessReference.reference w k f ap0 ap1 s p

def result (w : W) (shared : Bool) (f : Slice U8) (ap0 ap1 : Powers)
 (before : Scratch) (parts : Parts) : Result NHM_RegularKinds.Reply :=
 NHM_RegularKinds.go (child w f ap0 ap1) (NHM_RegularKinds.kinds shared) before parts

/-- Substitution of the complete CLOSED law respects fail/div and every
returning mutable state, including Err after earlier writes. -/
theorem source (w : W) (shared : Bool) (alpha : Slice E) (f : Slice U8)
 (ap0 ap1 : Powers) (before : Scratch) (parts : Parts)
 (s2 : w.variant=FIo_Native.transport.Variant.S2) :
 FIo_Native.weights.process_regular_kinds w shared alpha f 2#usize 64#usize ap0 ap1 before parts =
 result w shared f ap0 ap1 before parts := by
 rw [NHM_RegularKinds.cohort]
 unfold NHM_RegularKinds.reference result child
 have same : (fun k s p => FIo_Native.weights.process_kind w k alpha f
    2#usize 64#usize ap0 ap1 s p) =
   (fun k s p => NHX_ProcessReference.reference w k f ap0 ap1 s p) := by
  funext k s p
  exact NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2
 rw [same]

/-- Actual decoded complete post plus the CLOSED frame. The run premise is
internal child-clause elimination, not an admissible positive-root premise. -/
theorem returning (c : Context) (before after : Scratch) (parts : Parts) (reply : RU)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial)
 (observed : result c.w.value (NGM_GuardExact.guard c.w.value 2#usize)
  c.f.value c.ap0.value c.ap1.value before initial=ok (reply,after,parts)) :
 FIo_Native.weights.process_regular_kinds c.w.value (NGM_GuardExact.guard c.w.value 2#usize)
  c.alpha.value.to_slice c.f.value 2#usize 64#usize c.ap0.value c.ap1.value before initial=
  ok (reply,after,parts) ∧ NHX_RegularPost.Inv after parts ∧
 (∀ j,(∀ k∈NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize),j≠k.val) →
   parts.val[j]?=initial.val[j]?) := by
 have call := (source c.w.value _ c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
  before initial domain.s2).trans observed
 refine ⟨call,NIG_PairFrames.regular c.w.value _ c.alpha.value.to_slice c.f.value _ _
  domain.s2 domain.factors c0 c1 before after initial parts reply inv call,?_⟩
 intro j outside
 exact NHX_RegularFrame.source c.w.value _ c.alpha.value.to_slice c.f.value _ _
  domain.s2 domain.factors c0 c1 before after initial parts reply inv j outside call

#print axioms source
#print axioms returning
end AspisR1.NIW_AlignRegular
