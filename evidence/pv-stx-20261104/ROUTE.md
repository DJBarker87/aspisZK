# Route decision evidence (CLI help pending quiet-window release)

The ae1-2 translator source is b59d5188c082f704a418c7cb4e52ad69328002d1
plus the recorded accepted extensions. Eight inspected files match every
corresponding pv-cx2 source-recovery hash. The retained binary matches fda587d2.
See ae1/translator-identity.json for the original three functional regeneration
comparisons and ProverRwFull adapter comparison; none is newly rerun here.

No state-threading option occurs in the complete Main.ml Arg specification
(lines 83–263), nor a state option in Config.ml. Pure.ml's fun_effect_info
(lines 1591–1602) has only can_fail, can_diverge, is_rec. FunsAnalysis.ml
retains a historical stateful field but initializes it false, never sets it
true for opaque/trait calls, and SymbolicToPureTypes.ml (756–783) does not
propagate it. mk_output_ty_from_effect_info (1184–1190) wraps Result only.
State-error mentions at Pure.ml 1365 and 1701–1718 and the micro-pass comments
are therefore NOT evidence that this pinned build supports state-threading.
N91800 will supply verbatim CLI help under the same binary identity.
No new translator, patch, flag pretending to enable state, or edited LLBC is used.

The authorized fallback is being implemented as source syntax plus a small-step
world interpreter. Code.seq stores continuations; Code.loop stores source loop
state; Machine.run retains its running Config at cutoff. A reached primitive
runs at the current world; only .ok resumes, at its returned post-world. Source
fail/div, native panic/abort/resource faults, partial effects and pending are
separate and preserve state/events. This is a proposed construction until its
focused Lean checks complete, and a generic substrate even after they complete.

Important fidelity frontier: simplify_duplicate_calls_visitor
(PureMicroPassesGeneral.ml 640–678) factors repeated monadic calls to earlier
results. Config.ml 600 defaults drop_as_no_op=true. An interpreter of final
pure output alone cannot infer native event multiplicity or dropped destructor
effects. Each reached source construct needs inspection against its LLBC/source
and, where necessary, explicit effect reconstruction. This observation is not
a checked counterexample against a particular shipped source path, nor an
impossibility claim; the static source-frontier inventory is not such a proof.
The entropy syntax lift preserves the visible five external call kinds,
explicit loops, all emitted restoration continuations and all emitted errors;
its ordinary Result nodes and source drops/resources still need native binding.

Required next source frontier after entropy/account: prover.retry_attempt,
prove_masked_attempt, material/reserve/nonce/leaf/opening callees, op259's actual
sampler continuation, then op257 under its existing source-bound obligation.
The full entry must be constructed without adding a whole-helper run hypothesis.
OWNER/op227/op257, witness-independent resource/failure timing, and the separately
named V370/L3 residual remain. No trust field, observer or simulator changes.
No source_entry_world, five deployed projection theorem, or privacy row removal
is currently claimed.

Account's error mapping is also a typed request: ProverRwFull.map_err is
ExternalFuns.op12, so it must not be evaluated eagerly inside a Result node.
The account lift exposes that external point with its original callback instance
and result argument. This does not supply op12's native interpretation.
A mechanical alias check found no direct ExternalFuns alias in the entropy
lift's 13 finite Result nodes. This is a direct-name check only, not transitive
effect-freedom; the source/drop/resource qualifications above still apply.
