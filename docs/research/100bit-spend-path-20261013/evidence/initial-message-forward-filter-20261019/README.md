# Executable initial-message forward encoder and image filter

The maintained 1024-entry decoder now has an executable CPolynomial forward encoder and an equality filter. For arbitrary input q, a successful filter output re-encodes exactly to q. For every message m, filtering its actual encoding returns m. Public completeness uses fixed Nat-cast node sets of sizes 513 and 512; the new public theorem derives M31 characteristic from the existing ZMod-M31 algebra structure and discharges both numeric node bounds. It has no node-injectivity, -1-avoidance, characteristic or numeric-bound premises.

These are focused Lean 4.32 checks, with exact source/import/object hashes, compiler commands, source revisions, exit status, time, peak RSS, process swap and printed axioms in the retained receipts/logs. Only standard axioms occur. The decoder dependency was already published in commit dc7cf95ce and was reused without rerunning it. The source map supplements missing source paths in raw receipts without altering those receipts. No production source changed.

The original worker manifest is retained unchanged and contains stale descriptions; the actual theorem names and contracts in the Lean source and this packet govern. In particular, the earlier FilterV3 public theorem had explicit characteristic and numeric premises; InitialMessagePublicFilter discharges them.

Remaining boundaries: construction of interpolation polynomials and raw root states, whole extractor/list matching and spend-witness recovery, runtime/bit-cost bounds, sampler law, protocol/ROM/source composition, privacy and two-transaction release gates. This packet proves no complete 100-bit security statement.
