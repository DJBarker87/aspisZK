import F3K_OpeningSpine
import F3K_SourceQueryDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_PreparedSourceFields
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

variable {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash} {p : OraclePortCompactDraft.Parsed}
    {out : verifier.Prepared} {scratch : Array aspis_core.field.WideExact 29#usize}

theorem fields (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    out.variant=v.variant ∧ out.gamma=s.c.gamma ∧ out.kappa=s.c.kappa ∧
    out.alpha=Array.make 2#usize [s.c.alpha0,s.c.alpha1] ∧ out.rho=s.c.rho ∧
    out.queries=s.c.queries ∧ out.state=s.c.t6.state ∧ out.claim=s.claimValue ∧
    out.roots=sem.roots ∧ out.semantic_alpha=sem.alpha ∧ out.z=sem.z := by
  exact ⟨congrArg (fun x=>x.variant) s.output,congrArg (fun x=>x.gamma) s.output,congrArg (fun x=>x.kappa) s.output,congrArg (fun x=>x.alpha) s.output,congrArg (fun x=>x.rho) s.output,congrArg (fun x=>x.queries) s.output,congrArg (fun x=>x.state) s.output,congrArg (fun x=>x.claim) s.output,congrArg (fun x=>x.roots) s.output,congrArg (fun x=>x.semantic_alpha) s.output,congrArg (fun x=>x.z) s.output⟩

theorem query_binding (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    ∃ q,LiteralQueryRead.decode (out.queries.val.map (fun x=>x.val))=some q ∧
      (∀ j : Fin 22,(out.queries.val[j.val]'(by have len : out.queries.val.length=22:=out.queries.property;omega)).val=(q j).val) ∧
      (∀ j : Fin 22,(out.queries.val[j.val]'(by have len : out.queries.val.length=22:=out.queries.property;omega)).val<262144) := by
  have same := (fields s).2.2.2.2.2.1
  simp only [same]
  obtain ⟨q,decoded,coordinates⟩ := F3K_SourceQueryDecode.source D embed s.c.t4 s.c.t5 v.final_message
    s.c.queries s.c.queryCall
  refine ⟨q,decoded,coordinates,?_⟩
  intro j
  rw [coordinates j]
  exact (q j).isLt

#print axioms fields
#print axioms query_binding
end AspisR1.F3K_PreparedSourceFields
end
