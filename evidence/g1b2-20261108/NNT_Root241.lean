import NNT_Native241
set_option autoImplicit false
noncomputable section
namespace NNT_Root241
open Aeneas Aeneas.Std Result AdapterRw RSL NMS_R2N_Interpreted
open NMX_R9_StageTwo (L D V)
/-- Complete canonical241 candidate. Only original D1/D2 remain; every native
244 outcome and full064 observation is retained by Native241.full. No Ops,
child/law/library/success/representation premise is retained. -/
theorem parametric (choices : NMX_R4_Authentication.Choices)
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (h : RSL.NNT.LawRefines V R0 w)
 (h242 : TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate choices)) :
 TX2_241.RowSpec_241 L D (TAS.lib V R0 w) (NMX_R9_StageTwo.stage2 choices) := by
 intro a env domain
 unfold NMX_R9_StageTwo.stage2
 split
 · rename_i represented
   let n := NMX_R9_Args241.reify a represented
   have image := NMX_R9_Args241.roundtrip a represented
   have sourceDomain : TX2_241.Domain (TAS.lib V R0 w) (NMX_R9_ArgsNative241.args n.program n.accounts n.data n.slot) := by
    rw [image]
    exact domain
   have run := NMX_R9_Live241.source_member choices n.program n.accounts n.data n.slot env
   have law := NNT_Native241.full choices n.program n.accounts n.data n.slot R0 w h sourceDomain env _ run
   rw [image] at law
   exact law
 · exact NNT_Port241.root choices R0 w h h242 a env domain


theorem weak_instance (ch : NMX_R4_Authentication.Choices)
 (h242 : TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch)) :
 TX2_241.RowSpec_241 L D (TAS.lib V (fun _ _ => True) V.tx2auth) (NMX_R9_StageTwo.stage2 ch) :=
 parametric ch _ _ (RSL.NNT.lawRefines_weak V) h242

theorem canonical_instance (ch : NMX_R4_Authentication.Choices)
 (h242 : TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch)) :
 TX2_241.RowSpec_241 L D (TAS.lib V V.Root0 V.tx2auth) (NMX_R9_StageTwo.stage2 ch) :=
 parametric ch _ _ (RSL.NNT.lawRefines_canonical V) h242

example (ch : NMX_R4_Authentication.Choices) :
 TX2_241.RowSpec_241 L D (TAS.lib V V.Root0 V.tx2auth) (NMX_R9_StageTwo.stage2 ch) =
 TX2_241.RowSpec_241 L D V (NMX_R9_StageTwo.stage2 ch) := rfl
#print axioms parametric
#print axioms weak_instance
#print axioms canonical_instance
end NNT_Root241
