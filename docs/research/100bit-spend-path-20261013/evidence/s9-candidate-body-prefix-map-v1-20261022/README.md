# S9 candidate body prefix mapping

This packet proves that a successful execution of the actual generated candidate `factored_s2_libra_weights_loop.body` yields the same-call prefix data and maps its power-array and `scalar_factor` results into the retained concrete P6 model. The theorem also carries the exact four high-term calls and mapped term-array relation used by the downstream suffix proof.

The proof does not assume intermediate operation outputs as premises. Its inputs are the successful candidate body call, canonicality facts for the same seed and `ap1` reads, and the same loop-next witness. The explicit powers bridge, generated scalar-fold transport, and term-array bridge are imported as pinned owners.

This is a local model-link result for the selected candidate body. Candidate suffix/body completion, outer helper composition, source-library/caller correspondence, adoption, and the composed S9 theorem remain open.

The packet is source-only: no `.olean` or executable is included. The exact selected profile, direct-owner hashes, raw Lean log, controller, source revision, command, wall time, peak RSS, swap observation, and named axiom report are retained. `python3 -B check_packet.py` validates the packet without compiling Lean.
