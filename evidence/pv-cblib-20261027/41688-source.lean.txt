import R1Z.PV_CBL_ShaPadFixed
import R1Z.PV_CBL_FallbackTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadSuffixTotal
open PV_CBL_FallbackTotal
set_option autoImplicit false
theorem total (out : Array U8 64#usize) (suffix : Array U8 8#usize) :
    Total (PV_CBL_ShaPadFixed.sha_pad_suffix8 out suffix) := by
  unfold PV_CBL_ShaPadFixed.sha_pad_suffix8
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 0#usize) _ (PV_CBL_FallbackTotal.read suffix 0#usize (by decide)) ?_
  intro a
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 1#usize) _ (PV_CBL_FallbackTotal.read suffix 1#usize (by decide)) ?_
  intro b
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 2#usize) _ (PV_CBL_FallbackTotal.read suffix 2#usize (by decide)) ?_
  intro c
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 3#usize) _ (PV_CBL_FallbackTotal.read suffix 3#usize (by decide)) ?_
  intro d
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 4#usize) _ (PV_CBL_FallbackTotal.read suffix 4#usize (by decide)) ?_
  intro e
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 5#usize) _ (PV_CBL_FallbackTotal.read suffix 5#usize (by decide)) ?_
  intro f
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 6#usize) _ (PV_CBL_FallbackTotal.read suffix 6#usize (by decide)) ?_
  intro g
  refine PV_CBL_FallbackTotal.bind (Array.index_usize suffix 7#usize) _ (PV_CBL_FallbackTotal.read suffix 7#usize (by decide)) ?_
  intro h
  refine PV_CBL_FallbackTotal.bind (Array.update out 56#usize a) _ (PV_CBL_FallbackTotal.update out 56#usize a (by decide)) ?_
  intro out1
  refine PV_CBL_FallbackTotal.bind (Array.update out1 57#usize b) _ (PV_CBL_FallbackTotal.update out1 57#usize b (by decide)) ?_
  intro out2
  refine PV_CBL_FallbackTotal.bind (Array.update out2 58#usize c) _ (PV_CBL_FallbackTotal.update out2 58#usize c (by decide)) ?_
  intro out3
  refine PV_CBL_FallbackTotal.bind (Array.update out3 59#usize d) _ (PV_CBL_FallbackTotal.update out3 59#usize d (by decide)) ?_
  intro out4
  refine PV_CBL_FallbackTotal.bind (Array.update out4 60#usize e) _ (PV_CBL_FallbackTotal.update out4 60#usize e (by decide)) ?_
  intro out5
  refine PV_CBL_FallbackTotal.bind (Array.update out5 61#usize f) _ (PV_CBL_FallbackTotal.update out5 61#usize f (by decide)) ?_
  intro out6
  refine PV_CBL_FallbackTotal.bind (Array.update out6 62#usize g) _ (PV_CBL_FallbackTotal.update out6 62#usize g (by decide)) ?_
  intro out7
  exact PV_CBL_FallbackTotal.update out7 63#usize h (by decide)
#print axioms total
end R1Z.PV_CBL_PadSuffixTotal
