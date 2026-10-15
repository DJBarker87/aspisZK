# Independent evidence review

Reviewed the source, attempt log/receipt, target snapshot, dependency pins, object archive and checksum index for `R1LiteralSemanticMessageFacts`.

`valid_erased` proves that a literal message accepted by the constructor-validity predicate erases to a message accepted by the unified sampler's validity predicate at that row. `parseMessage_none_of_not_valid` proves rejection for a message invalid at the selected semantic row. The sole attempt `a` is green with two `#print axioms` reports, both listing only `propext`, `Classical.choice`, and `Quot.sound`. Source and object hashes, raw log count, runner pins, and all 16 checksum entries match.

The statements concern the model's constructor schedule; they do not establish byte-parser, accepted-proof, or source correspondence.
