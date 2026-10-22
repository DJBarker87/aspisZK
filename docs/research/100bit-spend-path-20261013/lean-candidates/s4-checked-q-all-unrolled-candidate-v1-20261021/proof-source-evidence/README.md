# Lean source-cut equivalence evidence

The candidate Rust wrapper was extracted with the pinned Charon/Aeneas tools. Its emitted `Q.from_limbs` body reads indices 0 through 3 and uses four nested `< P` checks. `CandidateAllEquivalence.lean` proves full `Result (Option Q)` equality with the retained `fromLimbsWithAll concreteAll` / state-threaded `allRun` model, including rejection behavior. The result uses only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

This is candidate-source-cut evidence. The Rust source cut is an isolated copy of the proposed body and its unchanged entry wrapper. The result does not prove that the frozen production method has been changed, that the candidate is equivalent to the production Iterator::all implementation, or that Rust std's `Iterator::all` corresponds to `allRun`. The S4 use site, EbyK push caller, and source/std adoption boundary remain separate.

Aeneas generated resource options (`maxHeartbeats`, `maxRecDepth`) were removed from the candidate Types/Funs copies before compiling. `check_packet.py` verifies that each adapted file is exactly the generated file with those two option lines removed. The generated external axiom template is not imported. The proof object is identified by SHA256 only and is intentionally not included.

Run `python3 check_packet.py` from this directory. The sibling candidate packet's `python3 check_candidate.py` checks the one-method Rust patch and differential tests.
