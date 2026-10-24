# ResumeRoles acceptance criteria (before execution)

Entry: codex/cx-prover-rw-20261023 at 8bd72836ffdab0818b01623a078913f35cd95722.
Own tools/evidence: resume-roles only. No shipped source changes, Kani (including
frontend), backend, ELF, full manifest, services/cache/other-owner mutation,
merge or push. Retain original packets. No new trust or premise changes.

1. Inspect complete old054 structured control: nested empty true arm, its
   enclosing block suffix, rejecting terminating successors, result local0,
   move operands and normal cleanup. Record source hashes and exact statements.
   Empty arm alone cannot establish missing success construction.
2. Before compilation, read-only admission requests 2GiB, with full live cgroup,
   process/service/container visibility. Sum populated finite frontier caps
   plus request must be strictly below55GiB. For every populated uncapped
   uncovered memory cgroup, subtract direct memory-enabled children's current
   and inactive_file, then subtract exclusive inactive_file from exclusive
   current. Add this resident reserve and7GiB OS/control to finite reservations
   and request; require less than physical RAM and available>request+2GiB.
   Unknown, inconsistent, negative or inaccessible data denies. Never retry a
   denied compiler or resource failure unchanged.
3. At most one new ordinary optimized cargo rustc invocation, fresh own stage,
   MemoryHigh1536MiB/Max2GiB/Swap0/Tasks64; repeat admission before and inside
   scope. Pin final inputs, revision, dependencies, tool/sysroot before/go/post.
   No cfg(kani): public source under prover_rw_resume_scalar only. Obtain both
   compiler-built and optimized MIR in this single invocation. No binaries in
   commits; JSON>5MB hash+size only. Record command/exit/wall/RSS/swap.
4. Bind draw's source locals to named aggregate destinations, resume's exact
   field/leaf construction and moved-from flags, bytes64 cleanup before return,
   rejection retry before leaf/field/64, error conversion, run's LIVE owner
   observation and separate explicit disposal. Never identify by bytes, index,
   address or retained child pointers. Include unwind without claiming it proved.
5. Bind scalar hook shared typed loans to each actual active Drop self place;
   end shared pre-loan before mutable zeroize, post-loan after it; only Copy
   scalars escape. Project only private disjoint statics and hook locals.
   Inspect concrete emitted hook calls/accesses/branches; enumerate the exact
   primitive semantic rule if no accepted producer proves projection. Reverse
   patch identity and finite Nat facts do not prove erasure. No generic wrappers.
6. Report inspected associations separately from compiler evidence, native
   mechanization and OS/world/controller obligations. Only an actually accepted
   concrete semantics producer can close native refinement. One focused packet
   audit after source/evidence; no unnecessary Lean. Budgets at entry Lean240/260,
   Kani59/60(reserved), Rust1/3(charged denied admission, compilers0),
   extraction54/56, backend15/16, ELF0/3; at most6 Lean,1 Rust,1 supported
   extraction this step; zero Kani/backend/ELF. Both targets not yet established.
