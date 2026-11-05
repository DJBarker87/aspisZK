import NIX_ObservedBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_ObservedCongruence
open Aeneas Aeneas.Std Result NIX_EmittedTypes NIX_ObservedBody

/-- Boundary equality propagates to the complete emitted Result. It is an
OPEN composition interface, never an assertion that the finish packet exists. -/
theorem boundaries {H : Type} (B C : Boundaries H)
 (parse : B.parse=C.parse) (publicTranscript : B.publicTranscript=C.publicTranscript)
 (begin : B.begin=C.begin) (finish : B.finish=C.finish)
 (D : aspis_core.digest.Digest32 H)
 (pubdata : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) :
 emitted B D pubdata bytes hash none=emitted C D pubdata bytes hash none := by
 have same : B=C := by
  cases B;cases C
  simp_all only [Boundaries.mk.injEq]
 rw [same]

/-- All failure/divergence/error/success outcomes are retained by the complete
Result equality; this projection introduces no accepted-output premise. -/
theorem result_cases {T E : Type} (a b : Result (core.result.Result T E)) (same : a=b) :
 (∀ value,a=ok (.Ok value) ↔ b=ok (.Ok value)) ∧
 (∀ error,a=ok (.Err error) ↔ b=ok (.Err error)) ∧
 (∀ error,a=.fail error ↔ b=.fail error) ∧ (a=.div ↔ b=.div) := by
 subst b
 exact ⟨fun _=>Iff.rfl,fun _=>Iff.rfl,fun _=>Iff.rfl,Iff.rfl⟩

#print axioms boundaries
#print axioms result_cases
end AspisR1.NIX_ObservedCongruence
end
