# Own input repairs

K001 failed before proof because the nested Rust module registration omitted an explicit path. Add #[path="NBV_multiproof.rs"] to the scratch registration. K003 is the corrected-input attempt; K001 is charged conservatively. No launcher/infrastructure change.
