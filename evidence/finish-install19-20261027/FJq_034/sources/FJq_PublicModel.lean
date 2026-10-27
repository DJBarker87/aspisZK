import FJq_PublicField
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PublicModel
open FIz_ConcretePack (embed)
abbrev K:=FIv_NativeValue.K
def common (c : PublicSourceRaw.Common) : R0P.Public K :=
  {variant:=.privateTransfer,anchor:=fun i=>(c.anchor i).val,
   nullifier:=fun i=>(c.nullifier i).val,assetId:=c.assetId.val,
   recipient:=none,change:=fun i=>(c.change i).val,withdrawalAmount:=none,
   nextPairIndex:=c.nextPairIndex.val,snapshotFrontier:=fun l i=>(c.snapshotFrontier l i).val,
   nextRoot:=fun i=>(c.nextRoot i).val,nextFrontier:=fun l i=>(c.nextFrontier l i).val}
def model : PublicSourceRaw.Public → R0P.Public K
  | .transfer c r=>{common c with recipient:=some (fun i=>(r i).val)}
  | .withdrawal c a=>{common c with variant:=.withdrawal,withdrawalAmount:=some (a.val : K)}
/-- The guarded parser mapping preserves every field of the public model. -/
theorem mapped (p : PublicSourceRaw.Public) (h : PublicSourceRaw.Canonical p) :
    SpendDataMap.mapPublic ExactBaseProjection.embed
      (SemanticPublicWire.toPublic (PublicSourceRaw.mapPublic p h))=
      SpendDataMap.mapPublic embed (model p) := by
  cases p <;> simp only [PublicSourceRaw.mapPublic,PublicSourceRaw.mapCommon,
    SemanticPublicWire.toPublic,SpendDataMap.mapPublic,model,common,
    Option.map_some,Option.map_none,FJq_PublicField.value,map_natCast]
  all_goals
    congr 1 <;> (try funext i) <;> (try funext j) <;>
      simp only [SpendDataMap.digest,FJq_PublicField.value,map_natCast]
#print axioms mapped
end AspisR1.FJq_PublicModel
end
