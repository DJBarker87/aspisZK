# ProverRwNativeDropABI: typed continuation experiment (unadopted)

Parent c42a29bc58c4d65dd96b0ec64adafe43d6d1ae3d; branch
codex/cx-prover-rw-20261023. This design precedes any new backend build.
Only private compiler candidates, new job modules and evidence are authorized.
No shipped source, tool installation, protocol, feature, verifier, security
contract, key or trust changes. Both release targets remain unestablished.

## Observed interfaces and source association

Pinned V5 LLBC (unchanged Rust Guard source) calls foreign function6,
core::mem::swap. Its signature is forall T, 'x, 'y,
(&'x mut T, &'y mut T) -> (), with Destruct<T> metadata. At the call,
T = Option<&'a mut u32>. The two call regions differ from the nested 'a.
Drop takes &'self mut Guard<'a>; generated forward output contains the
updated owner and a backward function for ending the outer borrow.

Pinned Rust nightly-2026-06-01 core/src/mem/mod.rs:785 implements
swap<T>(x: &mut T, y: &mut T) by typed_swap_nonoverlapping. Its safety
comment requires typed, readable, writable, non-overlapping locations.
Option::take(&mut self) -> Option<T> (option.rs:1900) uses
mem::replace(self, None). V5 does NOT call Option::take. It must not be
silently substituted for swap or claimed validated by the Guard regression.

Existing Aeneas.Std models are:
mem.swap {T} (a b : T) : T × T := (b,a);
Option.take {T} (self : Option T) : Option T × Option T := (self,none).
These expose the forward returned/updated owners only. For nested mutable T,
V5 expects swap : F -> F -> F × F × ((B × B) -> (B × B)). The first two
slots are the updated left and right owners; the third transports updated
nested referents at loan ending back to their original owners. In V5 F and B
both erase to Option U32. A type-correct extra slot alone proves nothing.
For take the forward old value and updated owner have DIFFERENT positions
from swap, and its backward relation depends on loan origins. No take adapter
is proposed or accepted here; unsupported nested instantiations must reject.

## Candidate: reuse ordinary move/borrow translation

Instead of extending the trusted stdlib with an invented continuation,
try lowering only exact, fully applied, safe core::mem::swap calls to LLBC
moves: move both reference operands into fresh reference locals; move *left
into fresh T temporary; move *right into *left; move temporary into *right;
write unit to the call destination; StorageDead both references and temporary.
This is a compiler-source transformation, never a generated Lean text patch.
Keep original regular precise Drop call, lifetime ends and original disposal.
No Guard name, numeral, destructor result, counter1 equation or callback is
inspected. Unknown identities/signatures, operand shapes, generics, unsupported
T, unwind paths and escaping loans remain rejection boundaries. Do not erase
Bottom or dummy bindings: each move leaves Bottom and existing StorageDead
must process that state. No destructor runs while moving the referents.

The typed relation must track whole values (including reference identities),
not just dereferenced output numbers. For any disjoint initialized locations
L,R holding a,b and arbitrary untouched heap H, the three moves yield L=b,
R=a,H unchanged, temporary Bottom. Every nested reference identity travels
with its containing value. No callback executes during these moves. A later
well-typed callback on swapped owners may update their referents; ending loans
must transport the callback's *entire* pair back through inverse permutation.
For arbitrary carriers F,B, arbitrary forward relation RF, backward relation
RB, and arbitrary callback k : F×F -> B×B, swapping the forward pair and
inverse-swapping the returned pair preserves the same per-origin relations.
The inverse is fixed by location provenance, independent of values/callbacks.
This relation is the obligation to test/prove, not a new hypothesis equating
native output to desired output. Generic permutation facts alone do not prove
the Aeneas interpreter's implementation of lifetime ending. Concrete full
Guard closure and counter theorem remain mandatory; a failed move route is
retained and unaccepted rather than bypassed with a new trusted ABI.

## Printer and validation order

Extract.extract_Switch ignores `inside` on Lean and relies on indentation;
this prints `ok match ...` with incorrectly scoped result typing. Honor
inside for Lean Switch (if and match), with explicit parentheses. Do not
change Result, source theorems or branch result types to hide this error.

First validate the smallest generic relation helper. Then unchanged ordinary
noDrop, entire actual minimal Guard Types/Funs and counter0->1 theorem, then
recursive/move/conditional/order/writeback shapes, one full-statement/axioms
import audit. Only standard axioms; no new limits or sorry/admit. No full
manifest. Native tests are reference behavior only. Selected64 and combined
escape/capture must reject unsupported source. No Zeroizing/provider work
before full minimal Guard and typed relation are green. Unwind/postfailure
cleanup and opaque/generic glue remain open even after normal-path success.

## Metadata, resources and budgets

Config.ml sha256 81dd9fdb863e2c5e05407991f680a1a3c33eb01c289bf309a67a6f50fa66b35d
sets drop_as_no_op=true. Main Arg.Clear maps -eval-drops to false. Commands
020/022 omit it; old false labels do not show non-no-op branch execution.
Retain old receipts unchanged; new assessment and source-pinned command guard
must precede any new extraction. No broad installed-backend unsoundness claim.

New ceilings: backend12/16, extraction35/44, Lean230/260, Kani44/60. Every
reserved failure is charged; no reset. Precheck owned barrier files/hashes
before charge; reviewed complete-hierarchy admission plus fresh populated
reservation +8GiB strictly below55GiB, cap6G/8G/noSwap/Tasks64 before go.
Reuse private cache; optimized OCaml release; no local cold build. Lean uses
existing stricter5G/7G and global lock outside22:30–14:00 London. Exact commands,
flags, source/dependency/binary hashes, exit, wall, RSS, swap and full axioms
belong in receipts. No current check repairs historical incomplete evidence.

Before/after: existing native/refinement/E1 theorem statements identical;
no assumptions added, discharged or concealed. Candidate is unmerged.
