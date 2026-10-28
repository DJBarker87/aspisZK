# V221/V222 explicit zeroize execution (D362 resume)

Target not yet established. No deployment or L3 premise removed.

Before: op122/op123 remain unspecified callbacks, without a proof that their
value projection includes the writes/fences performed by native zeroize.
After: PV_FXM_ZeroSelected installs both fields in the original ExternalFuns
carrier. Restoring exactly those two fields recovers the entire old record.
The scalar value projection calls the provided Default dictionary, including
its complete Result; array recursion sequences the supplied element callback
and retains every changed element. No generic trait-name-to-zero assumption.

The physical zero-byte law is stated at the exact byte dictionary appearing
in the prover. PV_FXM_ZeroConsumed imports the original ProverRwFullFuns and
proves its U8 DefaultIsZeroes dictionary and selected blanket/array dictionaries
are the installed ones. The emitted zeroizing secret arrays have N=32 or 64;
the theorem handles every representable N without concrete recurrence reduction.
Unused U64/Usize marker definitions alone are not additional erasure calls.

PV_FXM_ZeroWorld gives memory, write/fence counts, ordered events, allocation,
reallocation, deallocation, destructor counts and an arbitrary disjoint frame.
It proves every target byte zero, preservation outside the exact target range,
counts of N volatile writes and N compiler fences, no allocator/destructor calls,
and execution composition with the caller's post-write state. ZeroTrace proves
history = prior history ++ exact chronological write/fence trace, including
when the initial bytes are zero; its history grows by 2*N. Nonvacuity constructs
a world for every supplied frame. Scalar and array callback execution laws
thread this state, rather than merely asserting that the returned value is zero.

STRUCTURAL-ZEROIZE-GATE.json checks complete pinned zeroize-1.8.1 source bodies:
array iter_mut -> IterMut per-element call -> primitive default -> volatile write
-> SeqCst compiler fence. The owned element recursion retains every result;
no Aeneas iterator emission or discarded backward continuation is credited.
This is structural (K-1 substitute), over Rust volatile/fence primitive semantics.
At this level volatile writes cannot be elided; fences constrain compiler
ordering. No hardware memory fence is inferred.

The separate L3 binary audit must establish the actual machine-code erasure
and its scope, including compiler preservation, registers, spills and extra
copies where required by the observer. Neither this source gate nor the native
output test discharges it. Freed pages, persistent media and side channels are
not made invisible by these theorems. No observer or simulator is weakened.

The optimized zeroize-04 native differential compiles the actual pinned crate
and passes 1,280 paired arrays (N=0,1,2,32,64) and 1,280 scalar byte cases, with
nonzero input patterns, all-zero targets and intact adjacent sentinels. This is
finite validation, not an unbounded compiler/non-elision theorem.

Focused passes: ZeroWorld 35508; ZeroSelected 35510; ZeroTrace 35511;
ZeroConsumed 35512. All printed axioms are accepted standard axioms. Failed
focused attempts are retained as rejected, with no credit. No Kani used.

Disposition: explicit effect-aware byte source laws and original-carrier
installations supplied. Complete native-to-deployed execution and L3 remain P
obligations. Generic custom trait effects are not silently counted as proved
physical zero-byte laws, and no endpoint premise is reported removed.

Consuming destructor addendum: ZeroDrop.complete/caller_composition (35529)
threads the exact emitted array callback through Zeroizing::drop and consumes
the owned array. The source gate now also checks the complete Zeroizing Drop
body. zeroize-drop-06 passes 1,024 paired actual destructor cases using live
MaybeUninit storage; no destroyed owning value is read and no double drop occurs.
This remains finite validation, with the same L3 boundary.

The final source gate also token-checks the pinned core::default macro and
u8 invocation: Default for u8 returns literal zero, with no native world
read/write or error path. ZEROIZE-INSTANTIATIONS.json exhausts the emitted
blanket instances and literal array lengths.
