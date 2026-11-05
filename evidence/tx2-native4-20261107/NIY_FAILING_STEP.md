# NIY unsuccessful attempts

TX2:065 OPEN. Failed objects are excluded from acceptance and imports.

- L002: raw/first3 transport helper had a redundant reader-roundtrip rewrite; the goal had already normalized it. Removed that rewrite; corrected source passed L004. The failed diagnostic's sorryAx is not accepted.
- L005: `prefix` was parsed as a reserved Lean keyword. Changed the own new definition name to `first3`; no Kani name or verdict changed. Corrected compile pending.

- L011/L012: generic query continuation associativity stopped at tuple-pattern lets; explicit traversal L013 exposed the reduction point. L014's dsimp had no progress; L015 retained the same unresolved let after a transparency adjustment. No timeout or memory kill occurred and no failed object is accepted. L016 replaces rewriting inference with an explicit residual goal at each read/decode step.

- L017/L018: query continuation rewrite could not infer the tuple-pattern lambda under Aeneas literal-type proofs. Replaced it by a fully instantiated Eq.trans with the named continuation; L020 passed. L016 had already proved the generic ordered continuation through explicit residual goals.

- L051: weights port left reply abbreviation was not unfolded by simpa at the final theorem application. L052 explicitly unfolded NIL_StatePort.reply and passed with unchanged statement and standard axioms.

- K035: full arbitrary64-weight Box/Vec constructor timed out at the unchanged90s solver limit (wall94.795s, RSS6351688KiB, swap0); exit1 is NOT a semantic corruption failure. No credit; negative/rename of that timed-out shape are not run. Replacement: one selected payload window on the SAME valid arbitrary64-cell input, with scalar descriptor/guard facts; combine pointwise windows in Lean. Native final-field fact reuse retains its prior domain. No cap/timeout increase.
- L053: own mapError lambda lacked its Vec<Result> payload annotation. L054 added it, then exposed the final reply/local-continuation abbreviation mismatch. L055 unfolds those exact abbreviations and passes, unchanged statement.
- L063: own Lean binder used reserved keyword at. L064 corrected only binder spelling and compiled; exact native assertion quotes are being pinned in the subsequent source audit.

- L076/L077: generic raw3 continuation application did not infer the actual ops record/continuations. L078 unfolds that record and explicitly supplies both same-reader continuations; exact tail theorem passes. L079 then discharges NIL_ResumeComposition.source's tail premise, for the fresh reference only.
- K051: actual opening getter selected-byte test on arbitrary57607-byte proof timed out90s (wall93.624s, RSS2680356KiB, swap0). No credit; do not run its unchanged control or rename. Replacement separates descriptor/provenance observations from the byte-value projection obligation. Whole canonical_scan remains OPEN.

L088 was rejected: omega treated a raw UScalar literal as an unconstrained natural. L089 explicitly simplifies the fixed 32-byte cursor before arithmetic; no recursion/heartbeat increase. L080 representation failure was replaced by BitVec value extensionality in L082.
