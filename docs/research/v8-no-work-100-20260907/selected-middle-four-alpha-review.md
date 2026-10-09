# Four-final reconstruction of the canonical middle quotient

Status: kernel-checked on the capped Tailscale NUC; v2 is green.

Source: [SelectedMiddleFourAlpha.lean](experiments/SelectedMiddleFourAlpha.lean).
All five axiom-audit declarations contain only `propext`,
`Classical.choice`, and `Quot.sound`. The preceding checked
`SelectedMiddleUniqueness` source and artifacts remain frozen.

## Exact result

`Generic.reconstruct` takes only a finite alpha-node set and the disclosed
final vectors. At each natural message parent index it Lagrange-interpolates
the scalar final value and places the four polynomial coefficients into the
literal consecutive slot order. `reconstruct_local` proves that changing
final values outside the node set changes nothing.

`Generic.reconstruct_folds` proves that four distinct actual coefficient
folds reconstruct the entire natural message. It reuses the cached V7
`coefficientFoldLayer_apply`, monomial coefficient/degree lemmas and the
same Lagrange interpolation interface used by `ExactFoldRecovery`. There
is no encoder enumeration, dense concrete vector reduction or code-valued
received-word assumption.

The selected endpoint derives the requisite fold identities from actual
per-node `MiddleWitness` existence and the checked same-gamma uniqueness
theorem. It does not assume a candidate input or a supplied equality to a
convenient codeword. Each node may use different kappa and tau histories;
the final is always the actual alpha-adaptive final of the fixed execution.
The result identifies reconstruction with the classical canonical quotient
and identifies every further middle continuation with its corresponding
alpha fold.

## Explicit limits

The source event restriction is `forall alpha in nodes, exists Q,
MiddleWitness ... Q`. This includes the actual family/image/row/higher-root
and final gates plus support interval 200808..252847. Bare terminal
acceptance is not substituted for that predicate. In particular, four
accepted 22-query schedules do not supply a large common support, and
terminal acceptance does not automatically give query residual zero across
the scalar-suffix repair exceptions.

This is deterministic reconstruction from four disclosed final coefficient
vectors under the named branch restriction. It supplies neither access to
four such continuations, an oracle/fork sampler law, a new gamma cardinal
bound, a better soundness probability nor a payment witness. It also does
not turn the classical canonical analysis choice into an online prover
operation. Four alpha values recover coefficients, not the degree-six
first-discrepancy identity that required seven alphas in the earlier leaf.

Nor does same-gamma reconstruction supply a degree-28 message curve across
different gammas. Interpolating 29 arbitrary reconstructed messages does
not identify the remaining messages among 64 gamma continuations. The
`candEq` premise of `NearGammaOwnSupport` is still necessary; a separate
coherence theorem must derive it before any own-support count is used.

## Focused verification

Only this new target was compiled; the green uniqueness leaf and all V7
dependencies were reused from the pinned overlay.

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 12.79 s | 6,835,924 | 0 | Generic coerced-cardinality arithmetic and selected implicit-size unification failed; no theorem credit for failed declarations. |
| v2 | 0 | 2.95 s | 6,870,236 | 0 | All five axiom audits standard-only; both 977-entry provenance checks passed. |

The two v2 repairs were purely local: rewrite the known node cardinality
before applying `Nat.lt_succ_of_le`, and explicitly supply `(n := 256)`
instead of leaving the elaborator to infer the size from `4*n=1024`.
No mathematical hypothesis or conclusion changed, and no heartbeat,
recursion, memory or CPU limit increased. The exact failed v1 source,
manifest and log are retained alongside the successful v2 artifacts.

Transport used numeric Tailscale endpoint `dombarker@100.108.41.90`, with
`nuc.local` only as the pinned host-key alias. The resource preflight found
a separately capped V7 service with MemoryMax 12 GiB and MemorySwapMax 0;
the new target retained MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0
and CPUQuota 200%. Combined reservations were 22 GiB on the 66.7 GB host,
with 49.2 GB available at the final reservation check. Lean 4.32.0 used
`-j1 -M9500`, recursion 200 and 250000 heartbeats.

Source work followed revision `24571219239106fd6c769f60ad7fb49725bef936`;
local revision at evidence closeout was
`556a15569f0dc1d003cf32475091187b206447ec`. The reused runner retains its
explicit research pin `289d7356c78a4cd493fe61a54f9548f2a0c11298` and
borrowed V7 pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; each run's
manifest pins appended dependencies and the exact new source separately.
The successful terminal postflight reported `PROVENANCE_UNCHANGED=true`.
The compiler slot was then explicitly released to the next agent. All
listed attempt artifacts and the green olean are copied back locally.

| Artifact | SHA-256 |
| --- | --- |
| v1 source snapshot | `30d0e2b2d27fc06e901a419cf75497f5c58b507ae3668d0c1e9a971851c473de` |
| v1 manifest | `f9b7155418af4b80a9fb60fc605a2f1258e50dd985bf79584946dbd094de8aa2` |
| v1 log | `958d51071bfe9c2e121d0d02d84339ac6f3c72dd79b12805f783237c0c70e840` |
| Green source and v2 snapshot | `38b129aa21b6e1b8fb5cd5de3cb9f9f61b159843c585ec3b4bb22382bbe6b8e7` |
| Green olean | `11d15f1a5984a6a0d11a8ae9a7cdc58aa41f23ef5a79aca09ed00ef2f1f75f74` |
| v2 manifest | `5cf5c4ce4768a8f9cc8c50c67398a87dc075ea1465dd4c4628e3bba96c1131e1` |
| v2 log | `5ce79a8960de7adfb49ba510e02ab933328308c23ec6b12c01330d0521235f0e` |
| Inherited runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
