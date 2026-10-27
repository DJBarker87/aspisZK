# op259 circle retry

kani-resume5-circle-900-q01, checks::circle_sample_reference.
Ruling(i) single retry of old180s timeout:unchanged unwind40 and input scope,
900s limit, taskset0–3, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64.
Cached optimized Rust compilation, then one named CBMC bounded gate/Kissat.
Exit124,wall15:00.00:no verdict, no checked source-row counterexample.
Exact argv, revision/input hashes, GNU time metrics and separate cgroup sample
are in the gate receipt. GNU timeout RSS is wrapper rusage, not aggregate RSS.

Ten-minute review was recorded at observed elapsed682.654094seconds since
admission. Native verification remained active, sampled cgroup peak1895047168
bytes,swap0. Caps were unchanged; the explicitly authorized900s gate was allowed
to finish. The review did not infer correctness or a source law.

The scope was then confirmed absent. Exact observed own CBMC PID4024743 solver
file /tmp/external-sat4024743.J8AbKe.cnf,192936435bytes,was removed with UID,
PID-prefix and run-window checks. See solver-cleanup.json. No key path touched.
V265/op259 remains OPEN. Pole1024 is still queued after an uncharged reservation
refusal; the12th Kani run has not yet been consumed as of this stage record.
