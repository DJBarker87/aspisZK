import JHe_SdkParent
import JHe_WrapperReady
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_TX1Frontier
open Aeneas Aeneas.Std Result

/-- This is the remaining-child frontier, not the requested accepted1 theorem.
The premise is the actual installed child call, not a replacement SDK result. -/
theorem wrapper_of_child (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (saved : alloc.vec.Vec U8) (size : saved.val.length=1768)
    (child : AdapterRw.first_decoded (JHe_Natives.sdk base stage)
      (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize=ok (.Ok saved)) :
    S2W_D189Wrappers.first (JHe_Natives.first base stage) CPH_FixtureData.copy CPH_FixtureData.allocator
      JHb_World.e1 CPH_Program.verifier JHe_Natives.data1 ()=
        ok (.Ok (saved,JHe_WrapperReady.post saved,())) :=
  JHe_WrapperReady.source base stage saved size (JHe_SdkParent.source base stage saved size child)
#print axioms wrapper_of_child
end AspisR1.JHe_TX1Frontier
end
