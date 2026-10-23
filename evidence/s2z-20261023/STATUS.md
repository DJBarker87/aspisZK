# S2-Z oracle and order

Target: adopted owned AdapterRwModel callers, not the historical SDK-borrow caller.
Only new S2Z_ modules and this worker’s tools/evidence are permitted.

Stage 0: source and interface inspection complete. No shipped file changed.
No Lean/Kani/Rust or ELF build was run. Source pins: stage0.json.

Oracle is open: op43 is explicit and uninstalled. Required14 requires a total
raw-oracle law; CheckpointBytes5Inputs.Oracle requires only successful calls.
CallOrder/reachedPrefix are open: extracted pure Result operations contain no
clock or event carrier. The two transactions are separate function invocations;
source order within one invocation does not establish their history association.
Existing child value joins do not instantiate an effect/reachability port.

Next: per-call native syscall/ROM transport, then source cuts and the exact
remaining child/history schedule boundary. No new trust or security claim.
