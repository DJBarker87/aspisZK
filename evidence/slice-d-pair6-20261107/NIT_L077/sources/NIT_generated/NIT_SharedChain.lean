import NIT_CommonChain
import NIT_PairControl
import NIT_RefInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_SharedChain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

inductive High (c : Context) (w : Ref W) (parts : Parts) : RU → Result NR → Prop
 | rejected (e : FIo_Native.verifier.Error) : High c w parts (.Err e) (ok (.Err e))
 | returned (out : Result NR)
   (tail : NIT_TailChain.Trace w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress out) :
   High c w parts (.Ok ()) out

theorem high_interpreted (c : Context) (w : Ref W) (parts : Parts) (r : RU) (out : Result NR)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (ce : NHI_CellCanon.array w.value.extra) (trace : High c w parts r out) :
 afterHigh c w parts r=out := by
 cases trace with
 | rejected e => rfl
 | returned out tail =>
  change NIT_TailChain.sourceTail _ _ _ _ _ _=out
  rw [NIT_TailChain.source w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress s2]
  exact NIT_TailChain.interpreted w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress s2 size ce out tail

theorem high_exists (c : Context) (w : Ref W) (parts : Parts) (r : RU)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (ce : NHI_CellCanon.array w.value.extra) (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (cp : canonical parts) (ck : canonE c.kappa) : ∃ out,High c w parts r out := by
 cases r with
 | Err e => exact ⟨ok (.Err e),.rejected e⟩
 | Ok u =>
  cases u
  obtain ⟨out,tail,_⟩ := NIT_TailChain.complete w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress s2 size c0 c1 ce cp ck
  exact ⟨out,.returned out tail⟩

inductive Partial (c : Context) (w : Ref W) (parts : Parts) : RP → Result NR → Prop
 | rejected (e : FIo_Native.verifier.Error) : Partial c w parts (.Err e) (ok (.Err e))
 | failed (values : Powers) (e : Error)
   (call : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts=fail e) :
   Partial c w parts (.Ok values) (fail e)
 | diverged (values : Powers)
   (call : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts=div) :
   Partial c w parts (.Ok values) div
 | returned (values : Powers) (reply : RU) (after : Parts) (out : Result NR)
   (call : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts=ok (reply,after))
   (tail : High c w after reply out) : Partial c w parts (.Ok values) out

theorem partial_interpreted (c : Context) (w : Ref W) (parts : Parts) (r : RP) (out : Result NR)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (ce : NHI_CellCanon.array w.value.extra) (trace : Partial c w parts r out) :
 afterPartial c w parts r=out := by
 cases trace with
 | rejected e => rfl
 | failed values e call => rw [afterPartial,call];rfl
 | diverged values call => rw [afterPartial,call];rfl
 | returned values reply after out call tail =>
  simp only [afterPartial,call,bind_tc_ok]
  exact high_interpreted c w after reply out s2 size ce tail

/-- Each returning high child is fed precisely the caller's post-regular Parts;
its CLOSED post theorem supplies the next canonical invariant. -/
theorem partial_exists (c : Context) (w : Ref W) (parts : Parts) (r : RP)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (hf : NHI_TensorOuterStep.Factors w.value) (ce : NHI_CellCanon.array w.value.extra)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) (ck : canonE c.kappa) :
 ∃ out,Partial c w parts r out := by
 cases r with
 | Err e => exact ⟨ok (.Err e),.rejected e⟩
 | Ok values =>
  cases call : FIo_Native.weights.shared_high values w.value c.ap0.value c.ap1.value parts with
  | fail e => exact ⟨fail e,.failed values e call⟩
  | div => exact ⟨div,.diverged values call⟩
  | ok result =>
   rcases result with ⟨reply,after⟩
   have post := NIG_PairFrames.high values w.value c.ap0.value c.ap1.value parts after hf c0 c1 cp reply call
   obtain ⟨out,tail⟩ := high_exists c w after reply s2 size ce c0 c1 post.1 ck
   exact ⟨out,.returned values reply after out call tail⟩

inductive Shared (c : Context) (parts : Parts) : Result NR → Prop
 | failed (owner : W) (cells : CommonCells) (e : Error)
   (common : NIT_CommonChain.Trace c.w.value 17
    ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ) (owner,cells))
   (call : FIo_Native.weights.shared_partials c.f.value cells=fail e) : Shared c parts (fail e)
 | diverged (owner : W) (cells : CommonCells)
   (common : NIT_CommonChain.Trace c.w.value 17
    ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ) (owner,cells))
   (call : FIo_Native.weights.shared_partials c.f.value cells=div) : Shared c parts div
 | returned (owner : W) (cells : CommonCells) (reply : RP) (out : Result NR)
   (common : NIT_CommonChain.Trace c.w.value 17
    ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ) (owner,cells))
   (call : FIo_Native.weights.shared_partials c.f.value cells=ok reply)
   (tail : Partial c ⟨c.w.address,owner⟩ parts reply out) : Shared c parts out

theorem common_interpreted (c : Context) (hf : NHI_TensorOuterStep.Factors c.w.value)
 (owner : W) (cells : CommonCells)
 (trace : NIT_CommonChain.Trace c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ) (owner,cells)) :
 NIG_CommonLoop.common_reference c.w.value (Array.repeat 16#usize NHX_FilledZero.zeroQ)=ok (owner,cells) :=
 NIT_CommonChain.interpreted c.w.value hf 17 _ (owner,cells) trace

theorem shared_interpreted (c : Context) (parts : Parts) (out : Result NR)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (trace : Shared c parts out) : shared c parts=out := by
 cases trace with
 | failed owner cells e common call =>
  simp only [shared,common_interpreted c domain.factors owner cells common,call,bind_tc_ok];rfl
 | diverged owner cells common call =>
  simp only [shared,common_interpreted c domain.factors owner cells common,call,bind_tc_ok];rfl
 | returned owner cells reply out common call tail =>
  have hc := common_interpreted c domain.factors owner cells common
  have hs := hc
  rw [←NIG_CommonLoop.common_source] at hs
  have same := (NIG_PairFrames.common c.w.value domain.factors owner cells hs).1
  subst owner
  simp only [shared,hc,call,bind_tc_ok]
  exact partial_interpreted c c.w parts reply out domain.s2 (NIT_PairDomain.message_size _ _ _ _ domain) domain.extra tail

#print axioms high_interpreted
#print axioms high_exists
#print axioms partial_interpreted
#print axioms partial_exists
#print axioms common_interpreted
#print axioms shared_interpreted
end AspisR1.NIT_SharedChain
