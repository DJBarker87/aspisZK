# RPx helper repair

Authorized by the lead correction. All binders and the existential conclusion are unchanged. The original helper premise is ill-typed in the pinned cohort.

Before:
```lean
FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)
```
After:
```lean
FinishModel.finish R B D pub pre before challenges
  (RPz7_PhaseIso.observerToFirst obs) = ok (.Ok out)
```

The matching call to S1SemanticFinishBounds.finish_success receives the same transported observer. The existing observerToFirst is Option.map of contravariant callbackToFirst, defined by toVerifier. Its invertibility is proved by first_roundtrip_RPz7, verifier_roundtrip_RPz7, callback_first_roundtrip_RPz7, callback_verifier_roundtrip_RPz7, observer_first_roundtrip_RPz7 and observer_verifier_roundtrip_RPz7 in RPz7_PhaseIso. No carrier equality or new isomorphism is assumed. The helper uses observerToFirst explicitly; the successful-finish proof is applied directly on its retained carrier. The none observer at the direct descendant reduces to none.

All other descendant declarations retain their statements and proof bodies, with imports redirected to the fresh repaired closure. Root declaration namespace becomes AspisR1.RPx_Deployed; root type preservation remains subject to the mandatory byte gate.
