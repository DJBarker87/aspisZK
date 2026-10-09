# Programmed alpha candidate disposition — 2026-09-13

## Result

Every completed accepted exact-root execution now constructs the literal first
alpha candidate machine run at the causal oracle state and residual fuel
derived from that same execution.  The candidate input is proved to be the
source grammar's `boundary.digest ++ [1]`, then exhaustively classified
at both the oracle state frozen when the adversary returned its proof and the
actual residual state where the candidate query begins:

- a matching prior adversary query;
- an existing root table entry, with no matching adversary query;
- absence at the root but insertion during the verifier prefix; or
- absence at both cuts when the candidate call begins.

The result also exposes the actual successful `queryOracle` call for that
input and its exact one-record history append.  It therefore does not infer a
query merely from the script's first syntactic input.

The construction starts from the same-body `ProgrammedAlphaCut`.  It inverts
the successful compiled `postAlphaScript` bind, rules out an error-valued
candidate prefix from the successful continuation, and retains the exact
source and pre-alpha machine returns.  It does not accept an analysis-only
transcript, candidate digest, oracle state, or successful sampler result as a
premise.

The root corollary additionally retains the exact equality between the
adversary-returned body/record/digest and the selected accepted value.

## Checked declarations

- `programmed_alpha_cut_constructs_candidate_disposition`
- `returned_accepted_exact_root_constructs_programmed_alpha_candidate_disposition`

Both report only `propext`, `Classical.choice`, and `Quot.sound`.

## Focused evidence

Lean 4.32.0 jobs ran on the NUC through Tailscale in separate systemd user
scopes with `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`,
`RuntimeMaxSec=600`, `-j1`, and `-M8192`.

| Leaf | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `FSV8ProgrammedWholeAlphaCut.lean` importable artifact rebuild | 0 | 2.77 s | 6,758,956 KiB | 0 |
| `FSV8AcceptedExactRootProgrammedAlphaCut.lean` importable artifact rebuild | 0 | 2.88 s | 6,758,924 KiB | 0 |
| `FSV8ProgrammedAlphaCandidateDisposition.lean` | 0 | 3.84 s | 6,774,592 KiB | 0 |
| `FSV8AcceptedExactRootProgrammedAlphaCandidateDisposition.lean` | 0 | 2.62 s | 6,755,448 KiB | 0 |

The dependency artifacts were rebuilt with explicit `-o` outputs.  A first
downstream attempt exposed that earlier check-only commands had left an older
importable `.olean`; no downstream result from that stale artifact is counted.
This evidence records the corrected source/artifact provenance.

## Security implication and boundary

This closes the deterministic accepted-root-to-alpha-candidate-query and
endpoint-classifier handoff.  It does not assign probability to any of the
four dispositions.  The next gate must connect each constructor to the
corresponding actual ROM event: prior-adversary query accounting, cached
root-target accounting, a provenance/charge for insertion during the verifier
prefix, and genuinely fresh sampling with bounded retry and abort mass.  The
atomic two-query candidate sampler and its later legal continuation must
remain coupled to the same execution.

Hostile statement review confirmed that the old unconditional `Nonempty`
classification and unrelated-state defects are removed.  It noted two
deliberate remaining boundaries: the generic leaf's actor becomes literally
the verifier only in the accepted-root corollary, and the new endpoint
classification does not yet identify which earlier verifier-prefix query
introduced a target in the third branch.  No probability claim relies on that
missing provenance yet.

Payment extraction, the total global event partition, and literal Rust
refinement remain separate obligations.
