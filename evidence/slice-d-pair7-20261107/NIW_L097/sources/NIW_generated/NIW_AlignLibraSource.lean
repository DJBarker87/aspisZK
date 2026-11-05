import NIW_AlignLibraCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibraSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_LibraChain

theorem source (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (libra : Powers) (cl : canonical libra) (parts : Parts) (cp : canonical parts) :
 let observed := NIW_AlignLibraCollect.collect f libra 5 ({start:=0#usize,«end»:=4#usize},parts)
 FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f.value parts libra=observed.1 ∧
 Trace f libra 5 ({start:=0#usize,«end»:=4#usize},parts) observed.1 ∧ Post observed.1 := by
 have traced := NIW_AlignLibraCollect.trace f size libra cl 5
  ({start:=0#usize,«end»:=4#usize},parts) rfl (by change (0:Nat)≤4;omega) cp
  (by change (4:Nat)-0<5;omega)
 refine ⟨?_,traced⟩
 rw [NIG_LibraLoop.source]
 exact NIT_LibraChain.interpreted f libra 5 _ _ traced.1

#print axioms source
end AspisR1.NIW_AlignLibraSource
