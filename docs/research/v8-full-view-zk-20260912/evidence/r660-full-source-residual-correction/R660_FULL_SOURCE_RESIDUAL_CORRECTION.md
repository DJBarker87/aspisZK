# R660 full source residual correction

Status: focused green and prepared for root review. No file has been staged, committed, or pushed.

`R660FullSourceResidualCorrection.lean` states the full `Index 256` / 1024-coordinate source quotient-weight system. It accepts arbitrary full-support R and G channels, with no low-support premise. From explicit pointwise 256-block first-fold-zero conditions for both channels, all seven full source plain and structured relation equations, nonzero scale, and the R657 determinant/query conditions, it derives the required target `evalSeven` condition and constructs an extended R657 correction. The complete full source quadratic coefficient system is zero for every beta, including beta 0 and 1.

The theorem separately returns zero points, 271 sparse coins, modeled query values, 32 first folds, and inactive balance for the correction. It does not prove these observations are preserved for the complete combined G view. It does not construct R or G from legal same-public witnesses, establish the retained premises from selected native execution, prove the actual root or determinant law, establish a shared-oracle law or published-view simulator, or prove privacy, soundness, or end-to-end security.

The final focused run was `1791113639778909000`, source revision `1f98f0f8b8de392663bb78cc437420930582fd80`, source SHA-256 `a69264542fcf89116d0bd9792132e2ee611842e0650f54d8082432585203024c`, exit 0, wall 1.46 seconds, GNU-time peak RSS 3,305,608 KiB, swap 0. All three final axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The compiler emitted two harmless unused-`NeZero` linter warnings; no replay was run.

`supporting-readonly/r658-actual-residual-target-inventory.md` records the frozen source-prefix and legal-target gap and is not a theorem dependency. R658/R659 are held in their separate low-128 scratch archive and are not part of this release candidate.
