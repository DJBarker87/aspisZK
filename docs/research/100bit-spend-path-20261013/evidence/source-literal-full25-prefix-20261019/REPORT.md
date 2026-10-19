# First 25 source calls coupled to the literal sampler

The checked theorem retains one chosen source trace, its initial call and all 24 tail calls. It derives the initial empty frame and source post-prefix from actual strict parsing and public initialization, then proves literalPrefix equals sourcePrefix on that exact tail and reaches the actual final sampler state. Public byte encoding, oracle input and root representation links remain explicit. Later transcript rows, commitments/openings and full verifier acceptance are not covered.

The upstream TraceLift change only makes the existing literalPrefix definition public. InitialCall and Full25Prefix were then recompiled natively against the same exact public TraceLift object; both checks pass with standard axioms and zero swap. Their output hashes equal the original checked objects. The coherent pair used 4 GiB high/6 GiB max/SwapMax=0 scopes and fresh global admission. Focused checks took 2.608 s and 2.307 s; GNU max RSS was 4126980 and 4130116 KiB.

Original per-component source revision labels are preserved verbatim and include working-snapshot labels, not exact release Git revisions. Source/object hashes and direct dependency pins are exact. This publication does not replace the required final coherent release replay. The earlier v7 state-only result is a superseded diagnostic, not evidence for full prefix equality.
