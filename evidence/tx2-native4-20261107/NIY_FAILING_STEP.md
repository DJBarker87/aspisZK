# NIY unsuccessful attempts

TX2:065 OPEN. Failed objects are excluded from acceptance and imports.

- L002: raw/first3 transport helper had a redundant reader-roundtrip rewrite; the goal had already normalized it. Removed that rewrite; corrected source passed L004. The failed diagnostic's sorryAx is not accepted.
- L005: `prefix` was parsed as a reserved Lean keyword. Changed the own new definition name to `first3`; no Kani name or verdict changed. Corrected compile pending.
