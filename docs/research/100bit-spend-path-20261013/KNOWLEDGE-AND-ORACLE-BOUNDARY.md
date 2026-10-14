# Knowledge extraction and committed-word boundary

The conditional R1 Fiat–Shamir result does not yet certify knowledge of a
spend witness. Three distinct objects must be connected: the oracle-query
table, the words authenticated by the commitments, and a semantic trace
from which the wallet witness can be recovered. The inspected existing Lean
supplies useful pieces, but not that complete connection.

## What the existing extractors establish

`R0FS.extract` in `v8-r0-fs-20261006/lean/R0FS/Protocol.lean` and
`R0C.SemStatement.extract` in `v8-r0-close-20261007/lean/R0C/SemStatement.lean`
ignore their table argument and select a witness with `Classical.choose`
when one exists. Their `none` case is witness nonexistence. That proves a
logical existence interface, not efficient recovery of knowledge from a
prover. Many valid spend statements have a witness that an attacker does
not know, so this distinction matters for the intended application.

`R0P.input_note_extracted` in
`v8-r0-sem-proof-20261008/lean/R0P/Extraction.lean` is a different result:
given a suitable semantic trace and its gate/copy premises, it identifies
the secret key, salt and path stored in that trace and proves the note
equations. The R1 candidate-to-spend bridges reuse that semantic result.
They still need a justified way to recover the candidate trace.

The existing exact GS decoders in `Wide/MultiplicityThreeGS.lean` provide
membership and 99/100-candidate size guarantees. Their definitions choose
interpolation coefficients and filter the entire finite message space.
This is a mathematical decoder specification. Neither that finite filter
nor its `noncomputable` wrapper supplies a polynomial-time algorithm.
The current tree and inspected reference/Z8/Z8b branches did not surface
an executable GS decoder or a refinement theorem. The older
`v8-wide-reference-20261005/R0_SOUNDNESS.md` already leaves extractor
runtime unanalyzed. A practical on-chain decoder is unnecessary, but an
efficient extractor and a justified complexity bound are still needed.

The new `PartialJointList` projection result preserves the 100-candidate
bound for any selected lane subset padded with zeros. It supplies a bound
for retaining partial tuples during a proposed incremental lane merge;
it does not supply the efficient per-lane decoder.

## The current verifier interface omits terminal hash reads

`UnifiedVerifier.verifier` invokes the existing `FS2.verifier`. It runs the
33 sampler chains, then returns a Boolean `decision` of the final prefix
and message. That decision has no oracle-program interface. The model's
trace therefore does not include Merkle authentication performed inside
the terminal decision.

The Rust `query_with_geometry` instead calls `HashFn` for salted C1/C2
leaves, both authentication paths, and the intermediate-word commitment.
The transaction flow also hashes proof/public bytes and checkpoint data.
Those calls need a common oracle/address representation and trace/budget
accounting before the model can describe the implementation. Enlarging the
trace alone will not prove D3: the accepted values must be bound to words
fixed at the correct earlier commitment times.

The old R549/R552 path proofs are useful deterministic ingredients. They
show that two different openings at the same position with the same root
expose a collision in their complete literal hash traces. Their selected
digest width is 26 bytes, whereas R1 uses 32; their selected payload widths
also differ. They cannot be invoked as an unchanged R1 source theorem.
Even the correctly adapted path theorem would not construct a committed
word from a partial table. A root or child digest whose preimage had not
yet been queried also requires a causal preimage/guessing argument; a
two-existing-preimage collision alternative alone does not cover it.

The [finite-table recovery checkpoint](MERKLE-TABLE-RECOVERY.md) now makes
that alternative explicit: recover the exact leaf, expose a collision,
or identify a missing node/leaf preimage for a fixed root/child target.
The finite lookup is constructive. The later
[canonical oracle-program connection](CANONICAL-MERKLE-RECOVERY.md) derives
consistency from canonical queries in the full trace, proves opening-read
inclusion, and connects child and initial-C1 root targets to the existing
first-read events. The actual commitment-time prefix, C2/folded root cases,
common collision event, and source/protocol composition remain open.

## The round-table interface also needs justification

`FS2.D2` quantifies over arbitrary tables `T'` and `T`, rather than only
causally related tables from one execution. `D2TableBoundary.table_flip_cost`
now checks a consequence: if a prefix is doomed at `T'` and every next
challenge produces a non-doomed extension at `T`, D2 forces the round
error to be at least one.

This rules out silently replacing the old witness-nonexistence classifier
with a naive table-availability classifier: if changing the table alone
provides the witness and makes every challenge good, the old small-error
premise no longer holds. It does not prove that every knowledge classifier
is impossible. A concrete classifier must justify the actual quantified
premise, or a causal/IOP knowledge reduction must be provided instead.
The current conditional Fiat–Shamir theorem remains valid within its
stated premises; it cannot close knowledge merely by changing its extractor
argument.

## Concrete continuation

1. The generic terminal-oracle interface, exact trace decomposition, read
   inclusions and old-verifier specialization now compile in `OracleVerifier`.
   Lift the unified experiment/decoder arguments and instantiate the actual
   terminal program; those are not supplied by the interface result.
2. The 32-byte literal path and three salted leaf adaptations now compile
   in `Merkle32Path` and `Merkle32Leaf`. Identify all accepted source hashes
   with these preimages, including the folded tree's actual padded layout.
3. Define commitment-time table reconstruction with explicit handling of
   missing preimages. Prove later accepted openings agree with the fixed
   words outside precisely charged collision and preimage events. Carry
   the proof through the actual shared oracle and checkpoint lifecycle.
4. Supply an efficient list-decoding/extraction procedure matching the old
   decoder guarantees, then apply the already checked semantic witness
   extraction. Prove the round classifier and its knowledge conditions
   for this extractor, retaining the explicit query factor.

These are root-owned architectural obligations. A generic interface lemma
or an imported existence theorem does not discharge them.
The [focused reuse checkpoint](ORACLE-MERKLE-REUSE.md) records the exact new
interfaces and their remaining boundaries.

## External compiler route is also conditional

[Block et al., *Fiat–Shamir Security of FRI and Related SNARKs*](https://www.pratyush.site/publication/fsfriplonk/fsfriplonk.pdf),
Definition 3.13 and Theorem 3.15, distinguish round-by-round knowledge with
a polynomial-time extractor from soundness. Their BCS compiler requires
the corresponding IOP properties; its classical error includes
`Q*epsilon + 3*(Q^2+1)/2^kappa`. Its stated privacy bound includes
`4*ell/2^(kappa/4)` in addition to the IOP privacy error.

Our inference: directly citing that privacy bound with a 256-bit oracle
would not certify a 100-bit privacy error. A tighter dedicated analysis or
different parameters would be needed. The paper is not an instantiation
proof for Aspis, and the current conditional duplex collision bound cannot
be substituted for its full compiler accounting.
