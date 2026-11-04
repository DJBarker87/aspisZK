import NGC_FinishFrame
import NGC_KNE_Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_PreparationBoundary
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes3Namespaces OraclePortCkptAbi4Decode
/-- Exactly the prepared-field facts needed by the checkpoint writer. The
rho fact is also needed at the initial query invariant, before any loop call. -/
structure Fields (p : verifier.Prepared) : Prop where
 variant : (toPrepared p).variant=.S2
 queries : ∀ j : Fin 22,
  ((toPrepared p).queries.val[j.val]'(by simpa [(toPrepared p).queries.property] using j.isLt)).val<262144
 gamma : CanonicalWide (toE p.gamma)
 kappa : CanonicalWide (toE p.kappa)
 alpha : ∀ j : Fin 2, CanonicalWide ((toPrepared p).alpha.val[j.val]'(by simpa [(toPrepared p).alpha.property] using j.isLt))
 rho : NBF_PowerStep.Canonical p.rho
 semanticAlpha : ∀ j : Fin 10, Canonical ((toPrepared p).semantic_alpha.val[j.val]'(by simpa [(toPrepared p).semantic_alpha.property] using j.isLt))
 coordinates : ∀ j : Fin 4, Canonical (match j.val with
  | 0 => ((toPrepared p).z.val[0]'(by simp [(toPrepared p).z.property])).x
  | 1 => ((toPrepared p).z.val[0]'(by simp [(toPrepared p).z.property])).y
  | 2 => ((toPrepared p).z.val[1]'(by simp [(toPrepared p).z.property])).x
  | _ => ((toPrepared p).z.val[1]'(by simp [(toPrepared p).z.property])).y)
 claim : CanonicalWide (toE p.claim)
/-- OPEN obligation addressed to NFW. The successful output is the SAME p
returned by op7 after the SAME parse/scan; no fresh Prepared witness is allowed.
This is a named boundary, not an axiom and not an instantiated theorem. -/
def NFW_Obligation (ops : VTop_Stages.Ops) : Prop :=
 ∀ {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : Hash) (scratch : Array VTop_Stages.aspis_core.field.wide_exact.WideExact 29#usize)
 (p : verifier.Prepared) (g : Array VTop_Stages.aspis_core.field.wide_exact.WideExact 29#usize),
 (∃ parsed,ops.op3 proof=ok (.Ok parsed)) → ops.op4 proof=ok (.Ok ()) →
 ops.op7 D semantic proof hash none scratch=ok (.Ok p,g) →
 Fields p ∧ NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)
/-- Explicit transport from the query invariant's four-limb predicate. -/
theorem canonicalK (q : aspis_core.field.QM31) (h : NBF_PowerStep.Canonical q) :
 Canonical (toK q) := ⟨h 0,h 1,h 2,h 3⟩
theorem canonicalE (e : aspis_core.field.wide_exact.WideExact) (h : NBO_TailDomain.WideCanonical e) :
 CanonicalWide (toE e) := ⟨canonicalK e.c0 h.1,canonicalK e.c1 h.2⟩
#print axioms canonicalK
#print axioms canonicalE
end AspisR1.NGC_PreparationBoundary
end
