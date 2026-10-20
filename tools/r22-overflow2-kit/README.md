# R22 continuation contracts

Use `/tmp/r22-overflow2-venv/bin/python generate.py --check` from this directory
(or equivalent tree-sitter environment). Generator reads frozen git blobs and
emits an isolated dependency-free Cargo crate. Added contracts never change
shipped files. Body/context edits are listed in generated/source-pins.json.

Run only selected new targets on the host through run-host.py ATTEMPT HARNESS.
Each immutable attempt has its own 6G/8G/no-swap/64-task cgroup and aggregate
55GiB admission. Rust opt-level=3 and overflow checks are enabled. Time is in
compilation then one CBMC contract check; there is no dense elimination.

Contract attributes alone do not prove a domain: check the harness's backing
allocation, slice length and loop bound. See evidence/r22-overflow2-20261021.
