# Finish fission: concrete numeric consumers

This source-only addendum records two checked consumers that extend the frozen V2/V3 literal-range fission result.

`AspisR1FinishFissionCurrentNumericV1.s2_success_fission_current_numeric` starts from success of the S2 `finish_relation` under `finishUnrolledPolynomialOps baseOps`. It derives the two returned alpha indices, connects them to the round equation's private array slots, and discharges each round polynomial and field equation with the checked current polynomial/field owners. Its conclusion includes the literal two-round helper-loop result, canonical intermediate and final claims, both polynomial evaluation facts, and the two concrete numeric round equations.

`AspisR1FinishFissionOriginalNumericV1.s2_original_success_fission_current_numeric` takes success under `finishOriginalPolynomialOps baseOps`, transports it through the checked original-polynomial operation equality, then applies the first theorem. This uses the accepted original emitted-polynomial body adapter and current unrolled consumer source lineage. It does **not** establish that a frozen production verifier call reaches this model success premise; the caller/source bridge and the fission helper candidate adoption remain open.

The generated theorem owners compile under Lean 4.32.0 with the capped NUC runner. No generated binaries are included here. The V2/V3 fission dependency closure is recorded in the separate literal-range packet with manifest SHA `aa0756b14671eee957127ffde130cf50b11e552a0ed46ff6932b76a55ec79037`. The current polynomial callback/Horner closure is recorded in the source-only packet with manifest SHA `e9d53a3c8b05faabc99390704bbb75aba487be29345dcac1e21195d60b769a18`.

## Accepted runs

- V10 current numeric consumer: exit 0, 2.508 s, process peak RSS 3,704,048 KiB, cgroup peak 382,173,184 bytes, swap peak 0. Axiom report: `[propext, Classical.choice, Quot.sound]`. Source SHA `cb429655ff5f3432b47090b9b507b42124e5151e9d89447161351ef556e8911b`; object SHA `9d6dc30961cd024272a461006910018c67a0d670b78ee82e208340773d795a5b`.
- V15 original success consumer: exit 0, 2.609 s, process peak RSS 3,693,824 KiB, cgroup peak 375,140,352 bytes, swap peak 0. Axiom report: `[propext, Classical.choice, Quot.sound]`. Source SHA `611c6a9b8ef12c68559c4c59fa9500bae4c287fa77fa55546186e9cf716b65cf`; object SHA `1925dc83e9a2a727121fa47fb6692571021642b100da1cb2a7b2fcaed41af021`.

The failed v9 alpha rewrite and v11–v14 import-resolution attempts are retained in native attempt directories, not represented as successful evidence. V10 fixed the alpha representation mismatch by exposing the private alpha slot as `p.alpha.val[0/1]` before rewriting. V15 selected the original bridge's complete coherent import roots; its earlier attempts are environment/preflight failures, not Lean proof failures.
