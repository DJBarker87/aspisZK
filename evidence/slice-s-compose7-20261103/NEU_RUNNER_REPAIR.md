# Lane runner evidence repair

Own runners now preserve the exact host RUST_SHA256 manifest bytes per attempt,
without the stdout print newline, before the next attempt can overwrite the
latest copy. Both local copies and host receipt.source_hashes can be compared.
Earlier manifests are recovered read-only from the unchanged launcher's source
snapshots where available; missing evidence remains unresolved rather than
being replaced by an unchanged prover rerun.

After native scope completion and receipt recovery, each runner inventories
and deletes only its own NEU_tmp external-sat*.cnf and smt2_dec_problem* solver
files, recording path/hash/size. It never touches a cache, another lane or a key.
This also checks for any older own solver leftovers. No reservation, launcher,
shim, compiler, source gate or proof condition is modified. These are lane-owned
script/evidence repairs under rule11; validation is unchanged or stricter.
