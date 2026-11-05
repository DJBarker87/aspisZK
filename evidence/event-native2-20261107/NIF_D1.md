# NIC-D1 investigation

The frozen candidate::tx1 calls parse_shape, canonical_scan, prepare, batch_merkle, geometry and then query_loop in that order. canonical_scan checks echeck(q[672..800], false) for every opening i<22. Parser NGV/NGO packets validate the semantic-prefix rows; they are not the source of the opening folded-field check.

PROVED: NIF_ScanEntry.reached_scan (L003) derives SAME-proof op4 success from NHL_Tx1Stages.beforeQuery reaching its Context. No query/decoder success is assumed. NIF_ScanDomain.reached_fields (L005) installs Op4P_Install.sourceBody and uses its CLOSED scan_of_success to obtain canonicality of the SAME nested opening folded-field byte window, for every i<22. Only standard axioms. The source-level fact is not conditional on a successful field decode.

K001 fields_all_pure passes on all 32 canonical words of the fixed128 region, running the literal four-field from_fn expression. K002 reachable-digest control fails. Native purity is conditional on that stated byte domain; the Lean decoder/carrier installation is in progress. No reachable noncanonical deployed input has been established, and no input is constructed.

Retained work: identify the selected op4 installation at the physical deployed prefix (parent ordering remains external); connect canonical byte predicate to exact emitted decoder preconditions and each active NFS query index using CLOSED domain packets. The full generic NFS packet remains arbitrary-byte; it is not silently restricted.
