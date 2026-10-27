import F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SemanticInventory
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def semanticCoordinate {Hash : Type} (sem : r1_semantic.Verified Hash) (j : Fin 4) : aspis_core.field.QM31 :=
  let z0 := sem.z.val[0]'(by have h : sem.z.val.length=2:=sem.z.property;omega)
  let z1 := sem.z.val[1]'(by have h : sem.z.val.length=2:=sem.z.property;omega)
  match j.val with
  | 0 => z0.x
  | 1 => z0.y
  | 2 => z1.x
  | _ => z1.y

theorem remaining_source {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash}
    {p : OraclePortCompactDraft.Parsed} {out : verifier.Prepared}
    {scratch : Array aspis_core.field.WideExact 29#usize}
    (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    (F3L_SourcePrepared.numeric out).semanticAlpha=(fun j=>F3L_RhoMeaning.decode
      (sem.alpha.val[j.val]'(by have h : sem.alpha.val.length=10:=sem.alpha.property;omega))) ∧
    (F3L_SourcePrepared.numeric out).coordinates=(fun j=>F3L_RhoMeaning.decode (semanticCoordinate sem j)) ∧
    (F3L_SourcePrepared.numeric out).claim=
      AspisR1CurrentPreparedClaim.Concrete.decode (AspisR1ClaimPreparedBridge.toClaimE s.claimValue) := by
  exact ⟨congrArg (fun x=>(F3L_SourcePrepared.numeric x).semanticAlpha) s.output,
    congrArg (fun x=>(F3L_SourcePrepared.numeric x).coordinates) s.output,
    congrArg (fun x : aspis_core.field.WideExact =>
      AspisR1CurrentPreparedClaim.Concrete.decode (AspisR1ClaimPreparedBridge.toClaimE x))
      (F3K_PreparedSourceFields.fields s).2.2.2.2.2.2.2.1⟩

#print axioms remaining_source
end AspisR1.F3L_SemanticInventory
end
