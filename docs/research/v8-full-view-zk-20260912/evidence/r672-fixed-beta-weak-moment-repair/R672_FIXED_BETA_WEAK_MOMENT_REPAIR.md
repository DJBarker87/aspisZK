# R672 fixed-beta weak-moment repair

Status: focused green and lead-reviewed. This is an unpromoted candidate; no unchanged check was replayed.

For one explicit nonzero beta, R672 constructs a 13-coordinate residual correction from full 256-index R and G first-fold zero conditions, exactly three moment conditions, nonzero beta, scale, quarter and kappa, exact query-root hypotheses, and the explicit residual determinant. It proves all seven selected coefficients vanish at that beta, retains the full source p2 boundary, and preserves all three modeled point functionals, 271 sparse coordinates, inactive balance, 22-by-4 query roots, and 32 first folds. R675 supplies the full-extension moment and p2 algebra reused by the proof.

The correction depends on the selected beta and later query roots. This is fixed-prefix algebra only: it does not construct G before its commitment or justify moving a challenge-dependent mask change across commitments. The causal shared-oracle, seed, commitment, and published-view simulator gate remains separate.

The theorem does not prove an all-beta result. Beta zero is explicitly open. It does not derive the moment premises from legal same-public witnesses or H1, bind the field model to native source execution, establish a shared-oracle law or probability loss, construct a published-view simulator, or prove privacy, soundness, or end-to-end security.

R672 final run `1791116929324629000`: target `AspisV8R19/R672FixedBetaWeakMomentRepair.lean`, source revision `34701005fe240b4ea2bd534b42c1a027069937a8`, SHA-256 `10cf6dc90aaddadfc6c97ae732131d6f8e6ae7d00f0848df299da54cd0f7385c`, exit 0, wall 1.99 seconds, peak RSS 3,332,268 KiB, zero swap. Its full axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.

R675 final run `1791116831941913000`: target `AspisV8R19/R675FullCorrectionMoments.lean`, SHA-256 `855d23ab5ff2db6aa76cee0ebe1259d881d5ea05f5962ef7292448b023a90f0a`, exit 0, wall 1.35 seconds, peak RSS 3,295,260 KiB, zero swap; all three axiom reports are standard only.

The evidence retains all R672 draft attempts, explicitly marking earlier partial/sorry outputs as rejected, R675 failures and final result, exact snapshots, receipts, logs, runner and direct dependency pins.
