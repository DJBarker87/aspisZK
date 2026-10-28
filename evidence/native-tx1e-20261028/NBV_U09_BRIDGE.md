# NBV TX2 U09 bridge

**OPEN — stage 1 in progress.** Exact target: proof length57607; batch1/tree0..2; queries10..21 distinct<2^18; at most12 occupied entries within MAX_BATCH16; eighteen binary levels; sorted/deduped SAME queries; exact slot count/padding; ordered leaf/node digest calls and three roots from SAME Prepared/proof, including rejected prefixes.

Functions: private_leaf_hash_with_digest, batch_key_at, batch_keys, batch_leaf, batch_merkle, batch_merkle_values, batch_tree, opening, same_batch_index, same_batch_leaf, slot, sort_batch_keys, slot_offset, Arity::{bits,levels,width}, index_at, node_count, occupied_binary_parent, root_matches, sibling_binary_parent, value_at, verify_in_place, well_formed.

U00 remains a named lower-unit dependency, with runtime digest VALUE supplied by the existing SHA/H row; native obligation is exact slices and unchanged replies. Coherent digest/error slots are op43/op44, correcting inventory op48/op49. This unit cannot yet be CLOSED-CONDITIONAL on U00 alone: its own multiproof/keys/batch and caller-domain association members remain open. No other new hypothesis is hidden in that classification.
