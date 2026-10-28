# NBV K-1 re-establishment

Exact mitigation: evidence/kani-mitig-20261028/KMX_copy_stubs.patch, applied verbatim to NBV_src; SHA in NBV_INITIAL_HOST_PINS.json. KMX's Rust functions are unchanged. Each harness installs all reached slice/pointer replacements via kani::stub and enables --unwinding-assertions. Typed direct array assignments are included in the carrier/store checks. No field or SHA value model is introduced.

K003 restores NBJ K048/K050's arbitrary u32 prefix-copy assertion (same n/k/input quantifiers, corrected unwind34 for explicit loop). K002 negates the known last-word fixture's expected value: it must FAIL. NBM's generated native playback already passes that fixture; imported read-only, no new native fixture substituted. K001 is a charged pre-proof module-path error, not copy evidence.

Full-carrier helpers are checked separately from their small row windows: arbitrary full scratch and exact native digest pointer, selected byte, reply and one call; arbitrary prestate and one selected row-store coordinate. Each value/copy gate needs its matching negative control before credit. A successful gate never closes an unproved caller or complete unit by itself.

Inherited NBE leaf/key/sort gates will be rechecked with exact KMX substitutions, retaining original properties/domains. Inherited Lean model/induction proofs are imported, not reproved. Any timeout is excluded, split and never relaunched unchanged. All other inherited native copy-dependent results remain suspended unless explicitly mapped to a successful mitigated gate and negative control in the final table.
