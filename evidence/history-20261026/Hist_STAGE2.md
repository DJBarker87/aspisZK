# History stage 2: charged binding and source-indexed trace

Hist_ChargedBinding.binding_or_collision removes supplied read-provenance/log and
P2Prime from the local comparison theorem. It fixes the containing adaptive
source and selection function before H, appends four audit reads and preserves
the source result. A uniform WHOLE-source first-read budget Q gives the explicit
collision-event bound6*(Q+4)^2/2^256. Existing replay1040 plus this audit4 requires
Q+1044. This is a symbolic probability theorem; no source-global Q is invented.

Hist_WriterInitialized.installed_marker derives the initialized first-byte marker
from the exact successful Port3 writer call already exported by WAdm's original
accepted pair. No arbitrary checkpoint byte/marker premise is added there.
Hist_NativeReject lifts zero-gate rejection to the original native wrapper.

Hist_Store defines source-indexed runtime DATA effects: rejected transactions,
authorized foreign writes, the actual successful extracted stage1 on a loaded
checkpoint buffer, and the readonly stage2. Hist_StepProtection derives that each
such event preserves an initialized verifier-owned key. Hist_TraceProtection
permits arbitrarily many such steps and derives noInterveningWrite and byte
retention. Hist_Persistence constructs the existing CheckpointVersionBinding
with the REAL trace events and initial ledger, deriving savedAtCommit,
loadedAtEntry, noInterveningWrite. No empty history is substituted.

Scope: this is a checked operational interpretation of existing runtime
ownership/loading semantics plus actual source calls. It is NOT yet a proof that
an arbitrary supplied deployed accepted pair uses the same protected key, nor
that an arbitrary whole Solana execution is classified into this trace. That
source/runtime association remains explicit work; the structure is not counted
as premise removal by itself. Pool ASQ8/ASF8/verifier CP remain distinct.

Global ledger delta at this stage: removed NONE, added NONE to endpoint.
All6 target rows remain pending the concrete association/composition. No changed
security metric, carrier, quantifier or release artifact. A full-source actual
entrypoint guard fixture is compiling optimized on the host in the job's own
directory; this is compilation, not arithmetic/proof-generation work.

26 charged Lean submissions:24 Lean processes and2 predecessor-missing prelaunch
failures016/018, conservatively counted. Passing/failing snapshots retained;
all passing top-theorem axioms are standard only. No timed-out/memory-killed job,
unchanged rerun, package replay or cap change. The two dependent prelaunches were
submitted before predecessor errors were inspected; predecessor inspection is
now sequential. No launcher or monitoring infrastructure was altered.
