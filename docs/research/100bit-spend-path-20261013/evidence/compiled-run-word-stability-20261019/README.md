# Recovered-word stability through the actual recording compiler

The three recovered commitment words in a compiled recorded run equal the original run's words and the retained buildWords output. The proof derives equality of replay frames, reuses commitment_cut_eq for the three corresponding Merkle cuts, and applies wordsFromRawCuts extensionality. Recovered-word equality is no longer a postulated annotation assumption.

Row-validity through row 30 for original and annotated runs remains explicit. This is a focused working theorem, not the full actual-acceptance/alignment proof. Exit 0, 12.94 seconds, peak RSS 3,169,124,352 bytes, zero process swaps; both axiom reports contain only standard axioms. Exact source/object/import hashes, source revision and command are retained. No unified release replay was run.

The next theorem proves the actual compiled verifier's rounds equal the original run's rounds enriched by the words recovered from that compiled run. Only original constructor validity through row30 is supplied; compiled schedule validity is derived from constructor-preserving enrichment. This is the intended enriched transcript relation, not an unjustified equality to unannotated rounds. Exit 0; 7.16 seconds; peak RSS 3,133,636,608 bytes; zero process swaps; standard axioms only. The original schedule and source acceptance-to-Checks connection remain explicit.
