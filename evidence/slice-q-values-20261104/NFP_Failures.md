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

- K024: the combined geometry receiver/read window timed out at90s
  (wall95.45s,RSS2735404KiB,swap0). It is excluded, with no unchanged rerun.
  Replacement: one original read per TX start/length, via a fixed-array Vec
  scaffold. K025--035 separately control both inverse and line reads, on
  arbitrary cells/index, with matched failures and rename pairs.
- L028: the unsplit trace-erasure proof exhausted the default200000
  heartbeats. No limit was raised. L029--035 split the same emitted call
  sequence into head/front/back and compose the exact partial Result.
- L036: missing Canonical import; L037 adds NBF_PowerStep and passes.
- L038: NEV_AccumPacket joint Phase ownership conflict, retained as the
  explicit coherence finding. Candidate declarations were never checked or
  credited, and the candidate is stored as .lean.txt.
- L040/L043: reserved Lean tokens used as identifiers in draft helper
  statements. Corrected in subsequent attempts, with no unsupported credit.

The inherited NFM validator entrypoint was executed while checking intake;
its derived outputs were byte-identical (git diff for the inherited directory
is empty). Subsequent NFP validation imports validate() directly and does not
invoke inherited main/output generation.
