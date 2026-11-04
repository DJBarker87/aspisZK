# Excluded attempts and replacements

- K001/K002: own scratch module path errors. K003 corrects the path stated
  by rustc (`src/NFP_query.rs`). These compiler failures earn no native credit.
- L002: proof was incomplete after simplification; L003 closes the remaining
  definitional equality. No sorry theorem is accepted.
- L004: native and Stage2 field records are nominally distinct. Replaced by
  the existing headline FIp_DotsAdapter coordinate conversions; L006 passes.
- L005/L008: an extra tactic after all goals were solved causes exit 1.
  The extraneous tactics are removed in subsequent attempts; exit 1 is not
  accepted despite printed standard axioms.
- K011: full original caller G timed out at 90s, wall96.44s,
  RSS2290548KiB, swap0. Excluded; not renamed or retried. Replacement splits
  the actual dot-return cut: K007 prefix, K012 post-dot suffix; frame and
  model composition remain separate obligations. K012/014 pass, K013
  branch/return corruption fails, K015 exact-KMX copy control fails.

Verbatim receipt/launcher logs retain tool-generated trailing whitespace.
