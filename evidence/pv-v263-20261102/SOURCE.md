# V263 deployed-source classification

Worktree /Users/dominic/ZK/.worktrees/pv-runjoin, branch codex/pv-runjoin-20261026.
Starting revision b0b2d9dda8e22ee91e886b4ddf7da85daa7bf860. No other writer.

The named candidate tip is 8e450dab55887ad4481fc600a4b0551645725296.
It no longer contains host_work.rs. The candidate's frozen prover receipt
README names source checkpoint 9c131667ca00f4daae78da6299b09a9fe0d00da9;
THAT committed source contains the operation and both extracted callers.
The retained candidate host src copy's host_work.rs and native_workers.rs
SHA256 values equal that checkpoint exactly (frozen-source.json). Source inputs
are committed below inputs/, not excluded by .gitignore. This distinguishes
frozen-source association from a claim about all code at the current branch tip.

host_work.map is NOT a pure sequential map. It calls
pool::ordered_families(16, family), with force=true. The pool first reads ACTIVE
TLS. Nested worker calls use sequential collection; otherwise Active::enter
sets TLS and a scope spawns k=1..15, runs k=0 on the calling thread, and joins
all handles. Each run catches unwinding panics (the panic hook can already have
emitted diagnostics); Active's destructor restores TLS. Join errors are retained
as panic payloads. Chunks are consumed in family order and the first panic in
that order is resumed. Thread creation itself may panic before collection.
Allocation failure/abort, unwinding cleanup, TLS, OS thread state and scheduling
cannot be replaced by the value f(i). Callback source Results are VALUES in
Vec<Result<...>>: Err does not cancel other callbacks or workers. Nontermination
of a worker can prevent a join and thus the whole return. Worker-failure prefixes
and destructor effects must remain even if there is no source Result projection.

There are TWO range layers. The pool partitions its n=16 across 16 families
(one family per k). Each host_work family then partitions the original item
count n with q=n/16, r=n%16, a=q*k+min(k,r), b=a+q+(k<r).
Each family allocates capacity b-a and pushes callbacks in a..b; the outer
host_work allocates capacity n and appends families in order. The pool itself
also allocates handles, caught-result chunks and the family vector. Even an
empty original n does NOT avoid spawning or pool allocation on the nonnested
path. public-work-trace adds a TRACE Mutex, lock poisoning/unwrap and a push;
it is not selected by the deployed r1p-check + ct-host-prover features.

Reached project call sites (frozen lines):
* host_commitment.rs:242, stage=200, count=lanes.len(), closure
  (domain,messages,variant,lanes), T=Result<Word,r0::Error>. Validation of every
  lane precedes launch. The reverse/pop caller subsequently picks the first
  returned Err in source order. Both base/secure/wide lane results remain.
* host_sumcheck.rs:82, stage=100+round, count=28*2^(9-round), round=0..9,
  closure (oracle,point,round,assignments), T=Result<QM31,r1_wire::Error>.
  The counts are 14336,7168,3584,1792,896,448,224,112,56,28. Each callback
  calls evaluate_assignment; merge_evaluations handles inner returned errors.
  The Oracle is the actual generic caller, not an invented constant function.

ProverRwFullExternalFuns op257 and host_work.map preserve the full outer
Aeneas Result and inner Rust Result carriers, but have no post-world or event
return. opsNative preserves residual op257 (NativeFrames63.op257). The current
Sequential64.worker branch reuses the SAME world in its continuation. Installing
a pure callback there cannot by itself bind the stateful source described above.
EVH8 D550's Runtime model explicitly distinguishes source Result, runtime fault
and finite-fuel exhaustion, retains events and post-state, and uses partial source
projection. Any worker extension must do the same. No source binding, success,
termination, allocator restoration or privacy endpoint closure is claimed here.
