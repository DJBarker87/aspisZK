# Own input repairs

K001 failed before proof because the nested Rust module registration omitted an explicit path. Add #[path="NBV_multiproof.rs"] to the scratch registration. K003 is the corrected-input attempt; K001 is charged conservatively. No launcher/infrastructure change.

K027: own serial wrapper initially classified Kani's generic VERIFICATION FAILED line before its later "CBMC timed out" line. Repaired classification to inspect timeout first and clean only this job's solver temporaries. No source result changed, no timeout/cap raised, no timed-out source rerun. Opening follow-up changes to an installed 32-byte window, rather than a full symbolic proof observer.
