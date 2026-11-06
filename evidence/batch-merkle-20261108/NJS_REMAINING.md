# Remaining obligations — active work

Target not yet established. This is an interim inventory, not an early-stop report. Budget remains and independent members are in progress.

- TX1:065 parent_with_digest: leaf candidate assembled; combined gate pending
- TX1:077 private_leaf_hash_with_digest: leaf candidate assembled; combined gate pending
- TX1:078 batch_key_at: leaf candidate assembled; combined gate pending
- TX1:079 batch_keys: native/model/composed packet pending
- TX1:080 batch_leaf: native/model/composed packet pending
- TX1:081 batch_merkle: native/model/composed packet pending
- TX1:082 batch_merkle_values: native/model/composed packet pending
- TX1:083 batch_tree: native/model/composed packet pending
- TX1:084 canonical_scan: native/model/composed packet pending
- TX1:086 parse_shape: native/model/composed packet pending
- TX1:090 same_batch_index: leaf candidate assembled; combined gate pending
- TX1:091 same_batch_leaf: leaf candidate assembled; combined gate pending
- TX1:092 slot: native/model/composed packet pending
- TX1:093 sort_batch_keys: native/model/composed packet pending
- TX2:049 private_leaf_hash_with_digest: leaf candidate assembled; combined gate pending
- TX2:050 batch_key_at: leaf candidate assembled; combined gate pending
- TX2:051 batch_keys: native/model/composed packet pending
- TX2:052 batch_leaf: native/model/composed packet pending
- TX2:053 batch_merkle: native/model/composed packet pending
- TX2:054 batch_merkle_values: native/model/composed packet pending
- TX2:055 batch_tree: native/model/composed packet pending
- TX2:057 parse_shape: native/model/composed packet pending
- TX2:060 same_batch_index: leaf candidate assembled; combined gate pending
- TX2:061 same_batch_leaf: leaf candidate assembled; combined gate pending
- TX2:062 slot: native/model/composed packet pending
- TX2:063 sort_batch_keys: native/model/composed packet pending

Slice boundary: canonical_scan calls echeck (TX1:189), OPEN in NJO and outside this job list. Reuse NJC/NJJ cuts and CLOSED decoders; do not author an echeck row. batch_tree depends on verify_in_place TX1:127/TX2:093, owned by NJP; consume only after merge. These do not block the independent keys, leaf, shape and slot members.
