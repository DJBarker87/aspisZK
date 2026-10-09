# Alpha prefix-insertion provenance — 2026-09-13

## Result

The accepted exact-root alpha classifier now resolves the former
'introducedDuringVerifier' endpoint case into two source-shaped alternatives:

- an actual query record in 'historySince root sourceRun.oracle'; or
- an actual query record in
  'historySince sourceRun.oracle preAlphaRun.oracle'.

The record carries the verifier actor at the root specialization, the exact
'boundary.digest ++ [1]' input, and the output stored by the table entry found
at the candidate cut.

The generic lemma applies the existing V7 relative table provenance theorem
to each of the two consecutive 'runMachine' segments. A root-table member is
contradicted using the proved root lookup absence. The actor identity comes
from each segment's exact fresh-extension/history invariant; it is not an
actor-coverage assumption on the nonempty root table.

The resulting five alternatives are:

1. prior adversary query;
2. pre-existing root target with no matching adversary query;
3. the entry appears during the source/OOD/gamma segment, with a matching
   query record in that segment;
4. the entry is absent after the source segment and appears during the
   pre-alpha segment, with a matching query record there;
5. absence at the candidate cut.

## Security implication

This is new causal information about the actual accepted execution. The third
and fourth cases no longer denote an untraceable state difference: they
contain a matching query from the exact segment in which the candidate input
first became present. The exhibited record need not itself be the fresh call
that created the table entry; the formal statement deliberately does not make
that stronger claim.

No branch has yet been assigned probability. The record must next be connected
to the same root cursor's causal full-digest target event, and the
fresh-at-candidate branch to the routed complete duplex ordinary-sampler law.
The complete decoder uses up to four output/advance pairs; the first pair alone
is not a uniform-QM31 theorem.

## Focused evidence

Lean 4.32.0 ran on the NUC through Tailscale in separate systemd user scopes
with 'MemoryHigh=8G', 'MemoryMax=9G', 'MemorySwapMax=0',
'RuntimeMaxSec=600', '-j1', and '-M8192'.

| Leaf | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| 'FSV8ProgrammedAlphaPrefixInsertionProvenance.lean' | 0 | 2.98 s | 6,764,896 KiB | 0 |
| 'FSV8AcceptedExactRootAlphaPrefixInsertionProvenance.lean' | 0 | 2.67 s | 6,758,120 KiB | 0 |

A separate hostile statement review passed after requiring the source-cut
lookup to be explicit in both insertion cases. Its remaining wording caveat
is resolved above: the witness is a matching segment record, not necessarily
the creating record.

Both promoted declarations report only 'propext', 'Classical.choice', and
'Quot.sound' (the generic two-segment lemma does not require
'Classical.choice').

Several focused development runs failed before the final sources passed:
missing namespace imports, an overcomplicated list-membership helper, nested
conjunction construction, and failure to unfold source-run aliases at the
exact expected types. Each was corrected without weakening a premise or
conclusion.

## Remaining boundary

This checkpoint proves deterministic query provenance, not chronological
target-event inclusion. The next theorem must identify the alpha-marker answer
producing 'boundary.digest' in the exact exposure trace and show that either
the earlier 'digest ++ [1]' record is charged by the root causal target event
or the candidate is genuinely fresh and governed by the complete routed
sampler coordinates.
