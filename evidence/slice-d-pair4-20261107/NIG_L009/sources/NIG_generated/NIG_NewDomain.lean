import NGW_NewInterface
import NHI_TensorOuterStep
set_option autoImplicit false
namespace NIG_NewDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NGW_ConstructorArrays

/-- Coordinate maps retain the SAME constructor arrays. -/
theorem map_holds {A B:Type} {n:Usize} (f:A→B) (P:A→Prop) (Q:B→Prop)
 (a:Array A n) (ha:Holds P a) (step:∀x,P x→Q(f x)) :
 Holds Q (FIn_WeightsInstall.mapArray f a) := by
 intro b hb
 rcases List.mem_map.mp hb with ⟨a,ha',rfl⟩
 exact step a (ha a ha')

theorem q_canonical (q:FIn_WeightsExtract.field.QM31) (h:NGW_ConstructorQM.Canon q) :
 canonQ (FIo_Install.toQ q) := h

theorem factors (w:FIn_WeightsExtract.Weights)
 (hf:NGW_FactorWrite.CanonFactors w.factors) :
 NHI_TensorOuterStep.Factors (FIo_Install.toWeights w) := by
 have mapped:Holds (Holds (Holds canonQ)) (FIo_Install.toWeights w).factors :=
  map_holds _ _ _ w.factors hf (fun plane hp=>
   map_holds _ _ _ plane hp (fun row hr=>map_holds _ _ _ row hr q_canonical))
 intro k hk d hd
 exact NHI_ScalarDomain.canon_pick NHI_CellCanon.array _
  (NHI_ScalarDomain.canon_pick (Holds NHI_CellCanon.array) _ mapped k hk) d hd

theorem extra (w:FIn_WeightsExtract.Weights)
 (he:Holds NGW_ConstructorQM.Canon w.extra) :
 NHI_CellCanon.array (FIo_Install.toWeights w).extra :=
 map_holds _ _ _ w.extra he q_canonical

/-- Every successful constructor reply preserves the source variant. This
is a structural fact of the emitted body, including its loop/box boundary. -/
theorem variant (v:FIn_WeightsExtract.FInVariant)
 (alpha:Array FIn_WeightsExtract.field.QM31 10#usize)
 (z:Array FIn_WeightsExtract.circle.SecureCirclePoint 2#usize)
 (w:FIn_WeightsExtract.Weights)
 (run:FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) : w.variant=v := by
 unfold FIn_WeightsExtract.weights_new at run
 obtain ⟨points,hp,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨q8,h8,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨q9,h9,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨regular,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨factors,hf,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨boxed,hb,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 unfold FIn_WeightsExtract.Weights.box_from_parts at hb
 cases Result.ok.inj hb
 cases core.result.Result.Ok.inj (Result.ok.inj run)
 rfl

#print axioms map_holds
#print axioms q_canonical
#print axioms factors
#print axioms extra
#print axioms variant
end NIG_NewDomain
