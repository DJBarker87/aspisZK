import NIW_AlignPair
import NIW_AlignFrames
import NIW_AlignCommon
import NIW_AlignLow
import NIW_AlignLibra
import NIW_AlignFinal
import NIT_AllocatorChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_PairRoot
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

abbrev zeroParts : Parts := Array.repeat 7#usize NHI_Scalar.zero
abbrev oneParts : Parts := Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ONE

theorem repeated_canonical (x : E) (canonical : canonE x) :
 NIT_Cuts.canonical (Array.repeat 7#usize x) := by
 intro value member
 simp only [Array.repeat,List.mem_replicate] at member
 exact member.2 ▸ canonical

theorem zero_canonical : canonical zeroParts := repeated_canonical _ NHI_Scalar.zero_canonical

theorem one_canonical : canonical oneParts := by
 apply repeated_canonical
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.ONE
 unfold FIo_Native.aspis_core.field.QM31.ONE FIo_Native.aspis_core.field.QM31.ZERO
 simp only [canonE,canonQ,canonC,LPi_CMProduct.Canon]
 decide

theorem distinct : zeroParts ≠ oneParts := by
 intro same
 have cell := congrArg (fun xs : Parts => (epick xs 0).c0.c0.a.val) same
 change (0:Nat)=1 at cell
 omega

/-- Exact negative root result: the old argument cut cannot identify a fixed
regular post, even on a nonempty native cut domain. This does not refute the
implementation or claim that both records arise in native execution. -/
theorem old_cut_does_not_identify (w : Ref W) (alpha : Ref (Array E 2#usize))
 (f : Ref (Slice U8)) (scratch : Ref (Array K 64#usize)) (parts : Ref Parts)
 (ap0 ap1 : Powers) (common : Ref CommonCells) (shared : Bool)
 (power i : Nat) (l : PairEdges)
 (native : cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i l)
 (expected : Parts) :
 ¬ (∀ log,cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i log → log.regular_post=expected) := by
 intro identifies
 have hz := identifies {l with regular_post:=zeroParts}
  (NIW_AlignPair.regular_post_free w alpha f scratch parts ap0 ap1 common shared power i l _ native zero_canonical)
 have ho := identifies {l with regular_post:=oneParts}
  (NIW_AlignPair.regular_post_free w alpha f scratch parts ap0 ap1 common shared power i l _ native one_canonical)
 exact distinct (hz.trans ho.symm)

#print axioms repeated_canonical
#print axioms zero_canonical
#print axioms one_canonical
#print axioms distinct
#print axioms old_cut_does_not_identify
end AspisR1.NIW_PairRoot
