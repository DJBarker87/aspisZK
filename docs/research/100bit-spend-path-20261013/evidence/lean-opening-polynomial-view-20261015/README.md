# Opening polynomial view focused evidence

This bundle records the focused compile of `AspisR1.OpeningPolynomialView`. It defines a generic ascending-coefficient polynomial over `WideExact`, proves its coefficient, evaluation, and degree properties, then exposes polynomial views for the first and second seven-coefficient opening payloads. Both have degree at most six, and their `TwoRoundComparison.boundary` equals coefficient 0 plus coefficient 4.

Attempt a is a preserved failed proof-plumbing draft. Its complete log emits seven theorem-level axiom reports, four containing `sorryAx`. Attempt b is the final green compile: exit 0, 2.31 seconds, peak RSS 3,569,460 KiB, zero swap under the 4G/6G/0/128 cgroup. Its seven reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The result is a symbolic polynomial representation of typed opening coefficients. It does not prove that Rust Horner evaluation refines this model, nor prove acceptance or extraction. The direct imports, their source/object hashes, and the capped runner/environment are pinned in `source-manifest.json`; compiled objects are retained in a deterministic archive.
