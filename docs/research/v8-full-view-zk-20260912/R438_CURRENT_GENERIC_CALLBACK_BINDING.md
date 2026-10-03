# R438: retained actual gamma-callback method binding

R438 captures the same selected freeze source without monomorphization. It retains the actual gamma closure's FnMut method binding that the monomorphic extraction omitted. This is source and extraction evidence. No Lean check, runtime dispatch theorem, whole-fold execution theorem, privacy proof or soundness proof is claimed.

## Exact target and custody

Target: `R438GenericClosureDispatch.llbc`. Source revision at launch: `e0d03f10e3834608a06d3b62af3e2f7abfba8c4a`. SHA256: `76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6`; 3,518,851 bytes. Charon exited0 with `has_errors=false`, wall14.74 seconds, GNU peak RSS630,068 KiB and swaps0. Terminal cgroup peak496,250,880 bytes, swap0 and no OOM/high/max events. These distinct memory measurements are both retained. Axioms: not applicable to diagnostic extraction; no formal theorem was checked.

The extraction command changes from R437 only by removing `--monomorphize` and choosing a fresh destination. The pinned original Charon/rustc, selected source hashes, flags/features, locked/offline release settings and resource checks remain unchanged. The job used MemoryHigh5 GiB, MemoryMax7 GiB, MemorySwapMax0 and TasksMax128. No old successful capture, unchanged Lean check or regression was rerun.

## Source mechanism and captured route

Pinned `translate_closure_trait_impl` constructs the callback binder, then returns before inserting it when monomorphization is enabled. The known-implementation normalization pass requires a method-map lookup; an empty map leaves the call indirect. The monomorphic R437 capture has159 function slots:156 declarations and3 absent slots. Among the156 declarations,91 are TopLevel,60 TraitImpl and5 TraitDecl. The exact descriptor selector impl35/trait3/method0/non-default uniquely identifies Fun112. Both relevant method maps remain empty. Metadata uniqueness alone was not used as an execution lookup rule.

In the generic R438 capture, the gamma closure has a FnMut implementation47, trait9, method0 with an explicit binder to Fun284. The separate FnOnce implementation46 binds Fun283. Generic fold176 calls its FnMut clause0; the actual batch caller25 supplies implementation47. Complete typed argument/binder rows are retained. The batch call_mut shim24 calls25; this is distinct from the inner gamma call_mut284.

The source-operation inventory also retains batch25 initializing power from Global18, borrowing Local4 mutably, borrowing gamma through the shared receiver, and moving both references into Type65. Callback284 reads through these captured fields and writes the new power through field0. Complete place chains, calls and unwind subtrees are saved. These origins and writes are source descriptions, not a disjointness, allocation, lifetime or frame theorem.

Region annotations at the call, operand and binder levels are preserved, including their differences. The evidence does not erase these annotations or infer their equality. Method selection, generic substitution, call argument evaluation, borrow identity/restoration and function-frame execution still require justified correspondence.

## First remaining proposition

Prove the actual instantiated FnMut call executes the source closure with the correct accumulator, shared slice cell, mutable power and shared gamma, and restores the captured power through the returned borrow/frame. Connect that execution to the already proved R174 arithmetic step while preserving failures and divergence. The generic binding is evidence for this proposition, not its premise-free proof.

The actual raw-pointer loop, NotNull/ABI/provenance and read validity, every guard/cleanup/unwind, Vec::extend and full callback/oracle chronology through rho remain open. So do universal joint C1/H1/G compatibility, whole published-view simulation and shared-oracle losses, coherent original quotient extraction before beta and optimized-to-source acceptance. Genuine999,790 /999,532 CU and every security parameter remain unchanged. No benchmark, deployment, merge, transaction or wallet operation occurred.
