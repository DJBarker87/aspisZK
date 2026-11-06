# NKP failing steps and exclusions

Target not yet established.

* K001: actual checkpoint wrapper versus a second full decoder call on arbitrary bounded bytes timed out in CBMC, exit1,142.09484851593152seconds,2254784KiB,swap0. Retired, never rerun unchanged. Replacement K002..K045 isolates the actual wrapper's source-ordered tail with a full typed raw-child oracle and local returned-value observations; it changes the proof shape, not only a name.
* K003: the native corrupted bump control failed the exact intended assertion. Owned parser expected the word `assertion` instead of Kani's terse `Failed Checks`; parser corrected to require the exact assertion message. No proof rerun.
* The registry segment selector initially searched the borrowed-account spelling `.key` in the OWNED source, which uses `.key()`. The local IndexError occurred before K072 admission/submission. Corrected selector, then K072 submitted once. No infrastructure fault and no budget refund for an actual invocation.
* L003, L014, L016: failed Lean drafts (conditional simplification, ofFn indexing, untyped pair proof). Replaced by changed proofs L004, L015, L017. Current proofs use symbolic ofFn indexing rather than expanding concrete lists. Failed draft sorryAx output is EXCLUDED; current roots are audited separately.
* K080: ordered data/error/decoder-prefix positive PASS, but no matching control in this allowance. Explicitly UNPAIRED, no native row credit. A single error payload constructor suffices only for this partial map_err shape; no full raw-decoder packet is claimed.
* NKF K064/K067 timeouts and Result<Box> proof_for_contract/stub_verified failures were never rerun. No cap/timeout increase, writable static, function-pointer verdict or new runtime trust item.
