# Checked-Q candidate at the EbyK push slot

This packet composes the unrolled four-comparison candidate for `Q::from_limbs` through the actual emitted `fast_pairing.checked_q` call sequence and into the explicit emitted EbyK push model. It proves full-result equality for any `self`, `value`, and `scalar`, then specializes the Dot child to the retained `QRaw` backend and generated Dot control adapter.

The exported equations are:

- `checkedQCandidate_eq_concreteAll`: candidate `checked_q` equals the retained state-threaded `allRun` model for every QM31 input.
- `pushWithCandidateCheckedQ_eq_concreteAll`: the full `Result` from the emitted `pushWithOps` body is unchanged when the checked-Q callback is replaced by that concrete model, for any Dot callback.
- `candidate_push_eq_qraw_backend`: the candidate push with the retained generated Dot adapter equals installed `pushWithDotBackend QRaw` as a full `Result`, with no arbitrary checked-Q iterator predicate or Dot backend argument left.

The `checkedQCandidate` body preserves the generated `limbs_of → Q::from_limbs → Option::ok_or` order. Its only call replacement is the candidate `Q.from_limbs`; the existing source-cut theorem proves that replacement equal to the concrete `allRun` model. The raw generated Funs snapshot is included only for source inspection and is never imported. The Lean closure imports only the reviewed candidate equivalence, checked-Q model, concrete EbyK push model, and accepted Dot call-equality theorem.

The proof is a candidate/model result. It does not prove production adoption, full `Weights::pair` caller reachability, Rust `Option::ok_or` runtime correspondence, or the enclosing Rust `Iterator::all` standard-library contract. The differential test and source-cut evidence remain separate from those boundaries.

Lean 4.32 compiled the target with `-j1 -M4400`; exit status 0, 22.08 seconds, peak RSS 3,629,672,208 bytes, swap 0. The three `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The launch Git HEAD was not captured; exact Lean source bytes and imported owners are pinned in the manifest and direct-import map.

Run `python3 check-packet.py` from this directory to verify the packet files, source-body correspondence checks, candidate checker, dependency source pins, result receipt, and axioms.
