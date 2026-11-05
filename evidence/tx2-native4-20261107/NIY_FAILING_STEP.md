# NIY unsuccessful attempts

TX2:065 OPEN. Failed objects are excluded from acceptance and imports.

- L002: raw/first3 transport helper had a redundant reader-roundtrip rewrite; the goal had already normalized it. Removed that rewrite; corrected source passed L004. The failed diagnostic's sorryAx is not accepted.
- L005: `prefix` was parsed as a reserved Lean keyword. Changed the own new definition name to `first3`; no Kani name or verdict changed. Corrected compile pending.

- L011/L012: generic query continuation associativity stopped at tuple-pattern lets; explicit traversal L013 exposed the reduction point. L014's dsimp had no progress; L015 retained the same unresolved let after a transparency adjustment. No timeout or memory kill occurred and no failed object is accepted. L016 replaces rewriting inference with an explicit residual goal at each read/decode step.

- L017/L018: query continuation rewrite could not infer the tuple-pattern lambda under Aeneas literal-type proofs. Replaced it by a fully instantiated Eq.trans with the named continuation; L020 passed. L016 had already proved the generic ordered continuation through explicit residual goals.
