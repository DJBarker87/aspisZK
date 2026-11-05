import NIT_TailPhases
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_TailChain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairComposition
abbrev NR := NIT_ErrorTransport.NativeReply E

def zero : LowCells := Array.repeat 16#usize NHI_Scalar.zero

theorem zero_canonical : canonical zero := by
 intro x hx
 simp only [zero,Array.repeat,List.mem_replicate] at hx
 exact hx.2 ▸ NHI_Scalar.zero_canonical

def run (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers) (parts : Parts)
 (kappa : E) (lowAddress : Nat) : Result NR := do
 let low ← NIG_LowLoop.low_reference ap0.value ap1.value zero
 NIT_TailPhases.group w f ⟨lowAddress,low⟩ ap0 ap1 parts kappa

inductive Trace (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers) (parts : Parts)
 (kappa : E) (lowAddress : Nat) : Result NR → Prop
 | low (cells : LowCells) (out : Result NR)
   (trace : NIT_LowChain.Trace ap0.value ap1.value 17 ({start:=0#usize,«end»:=16#usize},zero) cells)
   (tail : NIT_TailPhases.Group w f ⟨lowAddress,cells⟩ ap0 ap1 parts kappa out) :
   Trace w f ap0 ap1 parts kappa lowAddress out

theorem interpreted (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) (lowAddress : Nat)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (ce : NHI_CellCanon.array w.value.extra) (out : Result NR)
 (trace : Trace w f ap0 ap1 parts kappa lowAddress out) :
 run w f ap0 ap1 parts kappa lowAddress=out := by
 cases trace with
 | low cells out trace tail =>
  have low := NIT_LowChain.interpreted ap0.value ap1.value 17 _ cells trace
  change NIG_LowLoop.low_reference ap0.value ap1.value zero=ok cells at low
  simp only [run,low,bind_tc_ok]
  exact NIT_TailPhases.group_interpreted w f ⟨lowAddress,cells⟩ ap0 ap1 parts kappa s2 size ce out tail

theorem complete (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) (lowAddress : Nat)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (c0 : canonical ap0.value) (c1 : canonical ap1.value) (ce : NHI_CellCanon.array w.value.extra)
 (cp : canonical parts) (ck : canonE kappa) :
 ∃ out,Trace w f ap0 ap1 parts kappa lowAddress out ∧ run w f ap0 ap1 parts kappa lowAddress=out := by
 obtain ⟨cells,low,_,cl⟩ := NIT_LowChain.complete ap0.value ap1.value c0 c1 zero zero_canonical
 obtain ⟨out,tail⟩ := NIT_TailPhases.group_exists w f ⟨lowAddress,cells⟩ ap0 ap1 parts kappa
  s2 size cl c0 c1 ce cp ck
 let trace : Trace w f ap0 ap1 parts kappa lowAddress out := .low cells out low tail
 exact ⟨out,trace,interpreted w f ap0 ap1 parts kappa lowAddress s2 size ce out trace⟩

/-- The emitted S2 tail, before loop replacement: exact two-fold branch and
all Result continuations. The variant test is proved, never assumed as Bool. -/
def sourceTail (w : W) (f : Slice U8) (ap0 ap1 : Powers) (parts : Parts) (kappa : E) : Result NR := do
 let low ← NIG_LowLoop.low_reference ap0 ap1 zero
 let value ← FIo_Native.weights.grouped_inactive_pair w f low
 let updated ← Array.update parts 0#usize value
 let isS2 ← FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant FIo_Native.transport.Variant.S2
 let weights ← if isS2 then FIo_Native.weights.factored_s2_libra_weights ap0 ap1 w.extra
  else FIo_Native.weights.twofold_libra_weights low w.extra
 let after ← NIG_LibraLoop.reference f weights updated
 let powers ← FIo_Native.weights.powers 7#usize kappa
 let sum ← NHX_FinalLoop.reference after powers
 ok (.Ok sum)

theorem source (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers) (parts : Parts)
 (kappa : E) (lowAddress : Nat) (s2 : w.value.variant=FIo_Native.transport.Variant.S2) :
 sourceTail w.value f.value ap0.value ap1.value parts kappa=
 run w f ap0 ap1 parts kappa lowAddress := by
 unfold sourceTail run NIT_TailPhases.group NIT_TailPhases.libra NIT_TailPhases.final
 simp only [s2,FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
  FIo_Native.transport.Variant.read_discriminant,bind_tc_ok,ite_true]
 rfl

#print axioms zero_canonical
#print axioms interpreted
#print axioms complete
#print axioms source
end AspisR1.NIT_TailChain
