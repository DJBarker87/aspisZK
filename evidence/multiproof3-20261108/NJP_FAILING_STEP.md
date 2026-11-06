# Failing steps

K001: compiler setup failure from own empty RUSTFLAGS (multiple input filenames). Replacement K005 uses --cfg NJP_good_argument; same validation, no timeout or memory kill, no semantic credit for K001.

L005: heartbeat timeout in congr tactic while comparing expanded Poseidon terms; no credit. Replacement L006 transports the symbolic seed equality with congrArg and unfolds only nodeCompress/digestOf; cap unchanged.

K023: full-range duplicate first/second payload-product observation TIMEOUT (95.048 s scope, 90 s solver, 1,823,840 KiB RSS, zero swap). K024 never launched. No credit. Replacement uses K021/K022 SAME pointer/index plus universal coordinate/byte prestate assertions, CLOSED child argument formation, and K015/K016 borrowed-window payload, with source-stage logging and a separate real write-window cut. No unchanged timeout replay or limit increase.

L031: attempted to reuse the one-height Stop invariant (n unchanged) across multiple completed heights. That statement is false: initial indices [0,1], no sibling nodes, first occupied step completes a height with n=1, then the next height stops on a missing sibling; n is 1, not initial 2. No proof/credit. Replaced by HeightProgress retaining exact partial scratch and monotone n<=initial n, not an unchanged-n hypothesis. This corrects a support statement, not the security contract or target.
