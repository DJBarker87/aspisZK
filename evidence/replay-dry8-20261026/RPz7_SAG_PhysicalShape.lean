import RPz7_SAG_NativeFull
import RPz7_SAG_ViewBytes
set_option autoImplicit false
namespace AspisR1.SAG_PhysicalShape
open Aeneas Aeneas.Std Result

theorem final (ops : VTop_Stages.Ops) (proof : Slice U8) (t : Cons_Native.Witness)
    (shape : SAG_NativeFull.Shape ops proof t)
    (start : ops.op21 = ok 8007#usize) (stop : ops.op20 = ok 10055#usize) :
    MultiproofConeCanonical.bytesOf t.v2.final_message.val =
      OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 8007 2048 := by
  obtain ⟨r0,folded,r1,fs,qs,h0,hfold,h1,hf,hq,read0,read1,readf⟩ := shape
  have sameStart : fs = 8007#usize := Result.ok.inj (hf.symm.trans start)
  have sameStop : qs = 10055#usize := Result.ok.inj (hq.symm.trans stop)
  subst fs; subst qs
  exact SAG_ViewBytes.final proof t.v2.final_message readf

#print axioms final
end AspisR1.SAG_PhysicalShape
