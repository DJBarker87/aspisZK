import NIT_TailLocal
import NIT_ErrorTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_TailPhases
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairComposition NIT_TailCuts
abbrev NR := NIT_ErrorTransport.NativeReply E

def final (parts : Parts) (kappa : E) : Result NR := do
 let powers ← FIo_Native.weights.powers 7#usize kappa
 let sum ← NHX_FinalLoop.reference parts powers
 ok (.Ok sum)

inductive Final (parts : Parts) (kappa : E) : Result NR → Prop
 | returned (powers : Parts) (sum : E) (out : NR)
   (powersLaw : FIo_Native.weights.powers 7#usize kappa=ok powers)
   (trace : FinalTrace parts powers 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) sum)
   (returnCut : NIT_TailCuts.returnCut sum out) : Final parts kappa (ok out)

theorem final_interpreted (parts : Parts) (kappa : E) (out : Result NR)
 (trace : Final parts kappa out) : final parts kappa=out := by
 cases trace with
 | returned powers sum out powersLaw trace returned =>
  have run := final_induction parts powers 8 _ sum trace
  change NHX_FinalLoop.reference parts powers=ok sum at run
  rcases returned with ⟨_,rfl⟩
  simp only [final,powersLaw,run,bind_tc_ok]

theorem final_exists (parts : Parts) (kappa : E) (cp : canonical parts) (ck : canonE kappa) :
 ∃ out,Final parts kappa out := by
 obtain ⟨powers,sum,source,_,trace,_,canonical⟩ := NIT_PowersInstantiation.powers7_final kappa ck parts cp
 exact ⟨ok (.Ok sum),.returned powers sum (.Ok sum) source trace ⟨canonical,rfl⟩⟩

def libra (f : Ref (Slice U8)) (weights : Powers) (parts : Parts) (kappa : E) : Result NR := do
 let updated ← NIG_LibraLoop.reference f.value weights parts
 final updated kappa

inductive Libra (f : Ref (Slice U8)) (weights : Powers) (parts : Parts) (kappa : E) : Result NR → Prop
 | failed (e : Error)
   (trace : NIT_LibraChain.Trace f weights 5 ({start:=0#usize,«end»:=4#usize},parts) (fail e)) :
   Libra f weights parts kappa (fail e)
 | diverged
   (trace : NIT_LibraChain.Trace f weights 5 ({start:=0#usize,«end»:=4#usize},parts) div) :
   Libra f weights parts kappa div
 | returned (updated : Parts) (out : Result NR)
   (trace : NIT_LibraChain.Trace f weights 5 ({start:=0#usize,«end»:=4#usize},parts) (ok updated))
   (tail : Final updated kappa out) : Libra f weights parts kappa out

theorem libra_interpreted (f : Ref (Slice U8)) (weights : Powers) (parts : Parts) (kappa : E)
 (out : Result NR) (trace : Libra f weights parts kappa out) : libra f weights parts kappa=out := by
 cases trace with
 | failed e trace =>
  have run := NIT_LibraChain.interpreted f weights 5 _ (fail e) trace
  change NIG_LibraLoop.reference f.value weights parts=fail e at run
  rw [libra,run];rfl
 | diverged trace =>
  have run := NIT_LibraChain.interpreted f weights 5 _ div trace
  change NIG_LibraLoop.reference f.value weights parts=div at run
  rw [libra,run];rfl
 | returned updated out trace tail =>
  have run := NIT_LibraChain.interpreted f weights 5 _ (ok updated) trace
  change NIG_LibraLoop.reference f.value weights parts=ok updated at run
  simp only [libra,run,bind_tc_ok]
  exact final_interpreted updated kappa out tail

theorem libra_exists (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (weights : Powers) (cw : canonical weights) (parts : Parts) (cp : canonical parts)
 (kappa : E) (ck : canonE kappa) : ∃ out,Libra f weights parts kappa out := by
 obtain ⟨reply,trace,_,post⟩ := NIT_LibraChain.complete f size weights cw parts cp
 cases reply with
 | fail e => exact ⟨fail e,.failed e trace⟩
 | div => exact ⟨div,.diverged trace⟩
 | ok updated =>
  obtain ⟨out,tail⟩ := final_exists updated kappa post ck
  exact ⟨out,.returned updated out trace tail⟩

def group (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) : Result NR := do
 let value ← FIo_Native.weights.grouped_inactive_pair w.value f.value low.value
 let updated ← Array.update parts 0#usize value
 let weights ← FIo_Native.weights.factored_s2_libra_weights ap0.value ap1.value w.value.extra
 libra f weights updated kappa

inductive Group (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) : Result NR → Prop
 | failed (e : Error) (call : NHM_GroupRoot.reference f.value low.value=fail e) :
   Group w f low ap0 ap1 parts kappa (fail e)
 | diverged (call : NHM_GroupRoot.reference f.value low.value=div) :
   Group w f low ap0 ap1 parts kappa div
 | returned (l : Tail) (after : Parts) (out : Result NR)
   (cut : groupCut w f low ap0 ap1 parts l after l.libra_reply)
   (group : NHM_GroupRoot.reference f.value low.value=ok l.group_reply)
   (factor : NHX_FactoredPacket.reference ap0.value ap1.value w.value.extra=ok l.libra_reply)
   (tail : Libra f l.libra_reply after kappa out) : Group w f low ap0 ap1 parts kappa out

theorem group_interpreted (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts) (kappa : E)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (ce : NHI_CellCanon.array w.value.extra) (out : Result NR)
 (trace : Group w f low ap0 ap1 parts kappa out) : group w f low ap0 ap1 parts kappa=out := by
 cases trace with
 | failed e call =>
  have run : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value=fail e := by
   rw [NHX_GroupPacket.source w.value f.value low.value s2 size];exact call
  rw [group,run];rfl
 | diverged call =>
  have run : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value=div := by
   rw [NHX_GroupPacket.source w.value f.value low.value s2 size];exact call
  rw [group,run];rfl
 | returned l after out cut groupCall factorCall tail =>
  have prefix := NIT_TailLocal.substituted w f low ap0 ap1 parts after l cut ce groupCall factorCall
  have mapped := congrArg (fun r : Result (Parts×Powers) => r >>=fun pair=>libra f pair.2 pair.1 kappa) prefix
  have next := libra_interpreted f l.libra_reply after kappa out tail
  simpa only [group,bind_assoc_eq,bind_tc_ok,next] using mapped

theorem group_exists (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts) (kappa : E)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (cl : canonical low.value) (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (ck : canonE kappa) :
 ∃ out,Group w f low ap0 ap1 parts kappa out := by
 cases call : NHM_GroupRoot.reference f.value low.value with
 | fail e => exact ⟨fail e,.failed e call⟩
 | div => exact ⟨div,.diverged call⟩
 | ok value =>
  have run : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value=ok value := by
   rw [NHX_GroupPacket.source w.value f.value low.value s2 size];exact call
  obtain ⟨l,after,cut,_,factorModel,groupModel,ca,cw⟩ :=
   NIT_TailLocal.local_log w f low ap0 ap1 parts s2 size cl c0 c1 ce cp value run
  obtain ⟨out,tail⟩ := libra_exists f size l.libra_reply cw after ca kappa ck
  exact ⟨out,.returned l after out cut groupModel factorModel tail⟩

#print axioms final_interpreted
#print axioms final_exists
#print axioms libra_interpreted
#print axioms libra_exists
#print axioms group_interpreted
#print axioms group_exists
end AspisR1.NIT_TailPhases
