# Lane-owned runner review

NGG wrappers copy the retained NFV lane-owned validation logic; S2W_run_host.py and the reservation launcher remain byte-identical. Own prefixes/budgets/cache paths were changed. One scope at a time.

Before the first Lean compiler launch, corrected the nested generated Python import regex: the inherited four-backslash source encoded a literal backslash instead of a regex whitespace escape. The corrected two-backslash outer string resolves actual import declarations and rejects missing objects. This strengthens dependency pinning and does not change proof validation. E001 imported no module: only its reference extraction and pinned Aeneas library were recorded.

K001 omitted the length-four hint assertion because its arbitrary-byte assume made that branch unreachable. K002 corrects the assertion placement and K003 is its matched failing control. K001 is superseded for coverage, never credited for length four. No timeout or memory failure was rerun.
