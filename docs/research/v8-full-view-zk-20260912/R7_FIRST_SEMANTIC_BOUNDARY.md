# R7 first chronological H1 boundary

Date: 2026-09-13.

Status: **Ticket C advanced to the paired C1/C2 commitment boundary before the
first semantic message**.

## Coin-use table

Each row refers to one of the 809 ideal H1 pad coordinates. “Yes” means that
the selected source value is causally influenced by that coordinate.

| Disclosure | Uses H1 pad? | Source-grounded reason |
|---|---:|---|
| C1 values/root | No in the ideal split | The H1 pad is allocated to H1 after C1, but the real construction derives both from one seed; independence requires an ideal-expander hybrid. |
| C2 values/root | Yes | C2 commits the encoded `[H1, G, D]` messages. |
| First semantic message | Yes | The selected terminal contains H1 evaluations and the first sumcheck message aggregates that terminal. |
| Point claims | Yes | All three selected H1 point entries are included; only the three D entries are omitted by the 84-field internal projection. |
| OOD claims | Yes | H1 is a committed layer-zero column used by the OOD relation. |
| `final256` | Yes | H1 enters the combined polynomial, quotient and folds. |
| q22 | Yes | The query schedule is sampled from the transcript after all preceding pad-dependent disclosures. |

This table is causal, not an independence proof. Fresh private entropy does
not reset the shared random oracle.

## First actual semantic disclosure

The selected generated source commits C1 root A, samples `lambda` and `chi`,
constructs and pads H1, then commits C2 root B using the same per-leaf salts as
C1. Only after B does `semantic_produce` form its first message. At round zero
it evaluates 28 samples, each the sum of the selected terminal over the other
nine Boolean coordinates, interpolates the degree-27 univariate, sends the 27
non-reconstructed coefficients, absorbs them, and samples the next challenge.

The selected callback is the literal
`evaluate_pool_v1_pair_forest_*_selected_masked_terminal_compiled_tag73_v1`
in `pair_forest_semantic_terminal.rs`. The generic name
`state_only_masked_semantic_oracle_value_v1` mentioned as a source pointer in
the handoff is absent at the pinned source revision, so no identity is inferred
from that name.

For fixed old C1 openings, mask-only openings, G, public data and already fixed
challenges, `composition_parts` obtains H1 at the selected point and passes it
to the copy terminal. The copy residual is affine in this H1 value, although
its fixed coefficients can depend nonlinearly on old C1 values. The selected
terminal is

```text
state_only_selected_mask_value(C1(z), mask_only(z), G(z), z)
  + eta * (
      eq(zc,z) * composition(z)
      + mu * H1(z)
      + mu^2 * (1-copy_active(z)) * H1(z)
    ).
```

Thus the first semantic message is a genuine fixed-linear/affine observation
of the remaining H1 pad only after the earlier state, challenges and other
coins have been fixed. Later genuinely linear H1 observations may be stacked
with it using one shared correction,
`[A P; B P] C = [A D; B D]`; they may not receive fresh independent H1 pads.

## Exact remaining chronological statement

The obstacle now precedes that affine semantic observation: C2 root B has
already committed pad-dependent H1 using the same hidden salt per leaf as C1
root A. A fixed-linear transport cannot retrospectively change this salted
commitment.

The nearest existing formal interface is
`V6PairedSaltHiding.paired_binary_packaging_hiding`. It treats two typed trees
sharing one hidden salt for a fixed public query set, but assumes a
`PairedSaltHidingHash` property and equality of the opened paired records.
`V5SaltedMerkleSimulator` explicitly leaves the bounded-query,
oracle-relative Merkle simulator/programming term open. Neither result covers
the selected adaptive V8 chronology.

The next theorem must construct a source-instantiated causal kernel/coupling
for the paired C1/C2 salted commitments in one coherent lazy random oracle.
Given the preceding C1-history coin transport and an ideal unused-uniform H1
pad, it must:

1. preserve the already exposed C1 root and prior oracle transcript;
2. transport the distribution of the C2 root while preserving the same salt
   shared by each C1/C2 leaf pair;
3. support later adaptive q22 openings with equal paired C1/C2 opened bytes,
   salts and authentication frontiers;
4. account for prior oracle queries, programming conflicts, shared-cache
   retries and the real-seed-to-ideal-expander loss.

Only after this kernel supplies the required conditional coin law may the R7
fixed-block helper theorem feed the first semantic-message transport. That
transport must then continue through point/OOD claims, `final256`, adaptive
q22 and the publication filter with one reused pad and explicit losses.

The current publication prototype remains reject-all: useful release still
needs a positive per-reachable-history release lower bound. No production
permit is issued by this milestone.
