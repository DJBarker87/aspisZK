# Own input repairs

K001 failed before proof because the nested Rust module registration omitted an explicit path. Add #[path="NBV_multiproof.rs"] to the scratch registration. K003 is the corrected-input attempt; K001 is charged conservatively. No launcher/infrastructure change.

K027: own serial wrapper initially classified Kani's generic VERIFICATION FAILED line before its later "CBMC timed out" line. Repaired classification to inspect timeout first and clean only this job's solver temporaries. No source result changed, no timeout/cap raised, no timed-out source rerun. Opening follow-up changes to an installed 32-byte window, rather than a full symbolic proof observer.

K028 combined leaf/new-row timeout: K029's matching salt-value negative control FAILS; no positive credit. K030–K039 were deferred before admission and replaced by post-hash decision/write/error cuts plus rebased-key/arity facts; no unchanged combined tree variant was run. Own serial wrapper saw the intentional defer as a missing receipt, with no submitted scope. It now handles deferred configs explicitly. These are own input/validation repairs, not host infrastructure changes.

Final validation was strengthened to compare every Kani receipt's exact KMX Rust source and patch hashes against the supplied patch. The own scope guard now also matches /usr/bin/python3. Source snapshots are retained for every attempt. No prover replay was performed for these validation-only repairs.
