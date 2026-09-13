# R5 stopping, release and loss boundary

Date: 2026-09-13.

Two focused Lean leaves now establish the generic stopping facts needed by a
repaired adapter:

- complete equality of paired attempt traces preserves all public events,
  release/failure and attempts used;
- a per-reachable-history conditional success lower bound `a` implies
  exhaustion at attempt cap `K` is at most `(1-a)^K`, without independence.

The existing adaptive-composition theorem supplies the chronological sum of
one-step distances. These results preserve one coherent oracle/history and do
not erase failed attempts or normalize on success.

## Source instantiation result

The current research publication boundary returns
`CompleteFullViewCoverageUnsupported` even when the raw precheck passes. It
therefore has release probability zero and exhaustion probability one for
every finite cap. No positive `a` exists. Retrying that result is both useless
and semantically wrong: unsupported coverage is terminal, not a random bad
schedule.

For a future useful adapter, every term remains explicit:

`epsilon_seed + epsilon_salt + epsilon_commit + epsilon_algebraic_bad +
epsilon_fs_conflict + epsilon_sampler_abort + epsilon_stopping +
epsilon_visible_attempts + epsilon_source`.

No term is assigned zero. The ideal uniform-subset geometry for the 768-pair
family is not the actual adaptive Fiat–Shamir schedule law and supplies no
end-to-end probability. The simulator and positive release lower bound are
blocked by the same missing source theorem identified in R3: a public causal
law/coupling for H1/C2 and semantic messages conditioned on the already
committed C1 history, followed by the remaining joint source maps.

Thus R5 generic probability machinery is checked, but the repaired abstract
protocol fails the required liveness premise and has no composable privacy
bound. This is an exact obstruction rather than an omitted numerical estimate.
