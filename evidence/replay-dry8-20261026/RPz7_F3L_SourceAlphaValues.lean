import RPz7_F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_SourceAlphaValues
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem alpha {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash}
    {p : OraclePortCompactDraft.Parsed} {out : verifier.Prepared}
    {scratch : Array aspis_core.field.WideExact 29#usize}
    (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    (F3L_SourcePrepared.numeric out).alpha=(fun j=>if j.val=0 then decode (toClaimE s.c.alpha0)
      else decode (toClaimE s.c.alpha1)) := by
  have array := (F3K_PreparedSourceFields.fields s).2.2.2.1
  let interpretation (ar : Array aspis_core.field.WideExact 2#usize) : Fin 2 → LiteralTranscript.E :=
    fun j=>decode (toClaimE (ar.val[j.val]'(by have h : ar.val.length=2:=ar.property;omega)))
  refine (congrArg interpretation array).trans ?_
  funext j
  fin_cases j <;> rfl

#print axioms alpha
end AspisR1.F3L_SourceAlphaValues
end
