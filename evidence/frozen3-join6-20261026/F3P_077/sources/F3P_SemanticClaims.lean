import F3P_SemanticDecode
import F3P_ClaimsMainRows
set_option autoImplicit false
namespace AspisR1.F3P_SemanticClaims
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem rows {H : Type} (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (pre : r1_wire.Prefix) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub bytes hash=ok (.Ok sem)) :
    ∃ (r : r1_wire.ValidatedRecord) (a b c : Array aspis_core.field.QM31 29#usize),
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize r 0#usize=ok (.Ok a) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize r 29#usize=ok (.Ok b) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize r 58#usize=ok (.Ok c) ∧
      (retainedSem sem).claims=Array.make 3#usize [a,b,c] := by
  obtain ⟨r25,r26,read25,extra,read26,before,claims⟩ := F3P_SemanticDecode.cells
    AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
    D pub bytes hash sem pre parsed success
  change ClaimsUnrolledFinish.claims std pre=ok (.Ok (retainedSem sem).claims) at claims
  rw [ClaimsUnrolledFinish.claims_value] at claims
  exact F3P_ClaimsMainRows.source std pre (retainedSem sem).claims claims

#print axioms rows
end AspisR1.F3P_SemanticClaims
