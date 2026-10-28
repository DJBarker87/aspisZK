# NCM focused proof repairs

- L001: existential log witness did not elaborate; made the exact transported node log explicit.
- L002: rewrite did not reduce an annotation let; changed to a focused `simp only` on the same equation. L003 passed.
- L005: `bind` in a simp list was ambiguous between Result and Program; qualified the Program bind. L006 passed.
- L007: arbitrary insufficient row fuel may diverge after a scratch update, whereas the observer defaults failure scratch to its original state. Added remaining-node fuel bound and NCM_RowsTotal.total; the actual level entry establishes it. L009 passed. No acceptance precondition added.
- L012: preceding simp had already expanded both annotation occurrences; removed a redundant rewrite. L013 passed.

All failed declarations are excluded. Printed sorryAx in failed Lean attempts is an elaboration-error artifact and has no closure credit. Final checked module sources contain no sorry/admit/axiom/native_decide or resource-option increases.

- L015: the guard conjunction reduced to True∧True before the if rewrite. Added the exact conjunction/literal-if reductions. L016 passed.
- L017: Lean inferred the original caller from the room proof; supplied the actual post-read caller explicitly. L018 passed.
- L023: the imported Aeneas do parser rejects dependent `if h`; expressed the logical view observer as a Result match. L024 then needed explicit subtype reflexivity; L025 passed.
- L024/L025: pre-launch SSH exit255 recovered through the existing 60-second retry path. No scope was resubmitted.
- L028-L030: nested do tuple lets obscured the leaf-step rewrite and a dsimp hit a scalar-proof transparency issue. Replaced tuple lets with explicit projections (same data/control), then rewrote the model-key form directly. L031 passed. No new elaboration/resource option or renamed harness.
- L034: escaped Rust cursor field accidentally used reserved `at` as a pattern variable; renamed only the local Lean binder. L035 passed. No Kani harness/module/function renamed.
