# Three-tau image separation on one reconstructed quotient

The kernel-checked `ThreeTauRecovery.three_tau_common_support` extends the seven-alpha construction without supplying Q or assuming image validity. Its hypothesis is one fixed received word and one shared set S of more than 255 matching fibres, three or more distinct tau values, and seven or more distinct alpha values for each tau. The ordinary prefix is shared before tau. Response0 may depend on tau, and final256 may depend on both tau and alpha. Each displayed actual carried prior is zero.

The construction obtains Q from the first tau's seven-alpha branch. Its received-word agreement on S then identifies **every** later final directly, using the selected final-code overlap cap. It never creates unrelated Q_tau objects and assumes them equal. The threshold remains 256 common fibres; 257 also suffices.

For each tau, the seven actual prior zeros force that tau's single first discrepancy polynomial to vanish. Its boundary is a zero evaluation of one degree-at-most-two image polynomial for the same Q. Three distinct tau values force that polynomial to be zero. Reusing `RobustImageGame.image_nonzero_any` separates all three scalar coefficients, producing:

- `claim = dot(ordinary,Q)`;
- `Q[1023] = 0`;
- `b*Q[1022] - c*Q[1021] = 0`.

The endpoint also retains Q's agreement with all four stored symbols on S, every adaptive final's exact coefficient-fold representation, and each first discrepancy identity. The ordinary equality refers to the one already assembled ordinary functional; it does not yet separate the inactive/three ordinary rows across kappa. No four-kappa endpoint is included.

## Scope

This is deterministic fork reconstruction, not a probability bound on a post-selected Q. Matching support, actual prior zeros and access to the fork branches are substantive hypotheses, not consequences yet derived from a successful q22 proof. The three-by-seven grid describes analysis observations, not added verifier rounds or proof-body fields. A shared mathematical word is explicit; no new authentication, fixed-word-from-root, replay or efficient-extractor theorem is supplied.

The received word may remain nonpolynomial away from S. Image constraints are proved for the reconstructed full quotient, not for an arbitrary oracle. Component original-code membership, early-C1 projection, semantic/ownership recovery and a checked payment witness are separate obligations. Prior-zero branches without shared matching support still do not suffice.

Source-shaped dependencies include the V7 exact stored encoder/inverse/fold identity and overlap bound, the literal compact discrepancy boundary, and image-weight/prior reference independence. The core never expands a concrete 1,024-coordinate polynomial to recover the three image coefficients.

## Evidence and cost

Source: `experiments/ThreeTauRecovery.lean`. Runner: `experiments/run_three_tau_recovery.sh`. The runner pins the new seven-alpha source/olean and checks all remaining research/V7 imports against immutable research `edb199c12fcc41f00330298b95b4736f60ac6f3a` and borrowed source `26a9cd4718aae9f9de7ef1c3394fb74a229085d5` before and after the focused leaf. It uses the existing laptop cache, Lean 4.32.0, `-M7000` and the aggregate 7-GiB guard. No NUC access, package build or other host job is used.

The first focused replay, `experiments/three-tau-recovery-v1.log`, completed with exit 0 and finished both provenance passes: 49.07 seconds for the Lean leaf, peak RSS 5,281,333,248 bytes, zero swaps. Both audited theorems use only `propext`, `Classical.choice` and `Quot.sound`. There is one harmless unused-section-variable warning, no `sorry`, no new axiom and no unchanged replay. Concurrent main remained read-only at `db7a1847b4197a03e7772ca68132ce8fb2d861bf`, with borrowed bytes checked against the immutable pin.

Source SHA-256: `79dbb8de3b097d6af59c072c2ce0fb11e88e42a8dc9c42e2336c6f274ad113b5`.

Olean SHA-256: `2bf2cb616f3a88396eacc6fb1fb31ece5c2f2e4ff2397dcf199a53dc0bb6e25d`.

Runner SHA-256: `2f307426402a55d25d2e85fe79399e66141fcbc77f633e1ce2a4159927550847`.

Source and runner are frozen after that successful replay. Reproduction from the research root uses the command below; the runner refuses to overwrite an existing log, so any justified future replay must choose a new evidence filename.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_three_tau_recovery.sh docs/research/v8-no-work-100-20260907/experiments/three-tau-recovery-v1.log
```

No changes to the protocol, proof body, verifier operations or production code occur. The body model remains 40,282 bytes. There is no CU or proving/extractor-runtime measurement. Quantitative fork production and its resource/probability accounting are the next decisive obligation; full-view ZK and Fiat–Shamir remain separate.
