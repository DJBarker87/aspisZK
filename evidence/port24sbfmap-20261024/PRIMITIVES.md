# Smallest remaining producers and review route

These are specification obligations, **not new Lean declarations, accepted
premises, or proved native laws**. No before/after theorem premise change was
made in this job. Before and after remain: external reserve interpretation has
no concrete post-Vec law; no actual helper equivalence is established. The
new evidence fixes emitted bodies/coordinates for a future proof.

## I. Missing identity is separate from semantics

Producer I1: recover the contemporaneous selected SBF rustc executable hash,
`core`/`alloc` archive hashes and rust-src manifest, with evidence that these
were the inputs for the current three receipts. The executable path is
`1.89.0-sbpf-solana-v1.52/bin/rustc`; the selected program/library IR and machine
hashes are already in `selected-implementation.json` and `binding-map.json`.
Required source declarations are Global's definition/Allocator implementation,
RawVec/RawVecInner/Vec fields, reserve/grow_exact/current_memory/set_ptr_and_cap,
resize/extend_with and the actual array-clone specialization. Package versions
and the v0 rustc symbol disambiguator do not determine these source bytes.

Producer I2: exact selected source/inline association. Generic Core reserve and
some Core filled bodies have no final out-of-line match. The concrete
Accumulator/BatchedWeights MIR plus root/library LLVM bodies and final symbols
narrow the cuts; final DWARF inline information was stripped. Under the existing
P7 source-to-SBF boundary, a reviewed source-instance association can use these
receipts once matching source identity is supplied. Do not assume a whole
helper's behavior to manufacture that association. A new compilation against
an unproven different sysroot is not an identity proof for these ELFs.

## II. Selected allocator primitive, not another arena model

Exact selected Rust entry (as named in current emitted MIR):
`unsafe fn GlobalAlloc::alloc(&self: &BumpAllocator, layout: Layout) -> *mut u8`.
Exact selected emitted entry:
`ptr @_RNvCscR3e5J6VSLN_7___rustc12___rust_alloc(i64 size, i64 align)`.
Exact native ranges: default/devnet [334408,334680), Pool [390432,390704).
Source/program, LLVM, linked/deployed and machine pins are in REPORT/binding-map;
selected SDK declaration bytes remain I1's dependency, not an invented hash.

Admission must give the actual mapped private arena at S=0x300000000 and
L=262144 (default/devnet) or32768 (Pool), a readable/writable aligned8 cursor
word, cursor c=0 or S+8<=c<=S+L, live allocations above the cursor, valid
nonzero Layout with power-of-two alignment, and the actual integer-to-pointer
provenance/accessibility rule. Header, stack scratch, caller value and prior
allocations must be separately admitted/disjoint as required by accesses.
Valid Layout is a caller obligation, not “allocation succeeds”.

Smallest missing rules sufficient to attach Port22's arithmetic/frame facts:

1. `load_u64_le(M,S,H) -> (c,M,H)` on an admitted cursor read. Interpret actual
   native/Rust load, not a caller-supplied c unrelated to memory.
2. `int_to_ptr(w)` / `ptr_to_int(p)` and native pointer addition identify the
   admitted arena byte address for the selected casts/dereferences, with no
   forged permission from numeric equality. No global provenance axiom.
3. `store_u64_le(M,S,q,H) -> (M[S..S+8 := le64(q)],H)` when admitted. Specify
   exact footprint, order and any possible fault/abort prefix. This is the
   selected cursor store, not a whole-heap identity law.
4. Interpret the selected wrapping/saturating ALU and branch operations under
   the admitted Layout. Port22 `candidate_word` already supplies the integer
   arithmetic result; no reproof is needed. Cursor-store/native association
   then consumes `alloc_outside` and `success_interval`.

Derived target after those rules: q=(sat_sub(c==0 ? S+L : c,size)) & (-align mod
2^64). q<S+8 returns null without a cursor store; otherwise the actual cursor
store writes q and returns the accessible pointer for q. All other memory
outside the word is framed. Do not assume this derived target as a primitive.

In the actual artifact there are no call/callx slots inside this shim. To
conclude preservation of the oracle history, first interpret the reached
load/ALU/branch/store/return steps in the execution effect model. Syntactic
absence alone is not `nativeNoHash`. Faults may occur at loads/stores under
insufficient admission; those are not successful executions with arbitrary
outputs. Earlier caller observations remain in H on every prefix.

## III. Header field and temporary result primitive

Current emitted specialized reserve signature is fully retained; its entry
argument self is a 16-byte, align8 RawVecInner region, len specialized0.
A selected-layout admission must associate native cap address self+0 and ptr
address self+8 with MIR's logical RawVecInner fields; associate len with the
actual surrounding Vec, separately from output/temporary storage. MIR's buf
reborrow must preserve exclusive access and pass the actual old len value0.
This is missing association, not a consequence of an external `Result<Vec>`.

Small remaining rules are load/store for these specific admitted eight-byte
fields, typed discriminant interpretation and the reborrow/call/return move
rule. The native stores must be those observed instructions, not witnesses
chosen after learning the desired poststate. Distinct cap/ptr/len words and
private cursor establish the byte disjointness required by Port22 VecFrame.
Interpret finish_grow's separate 24-byte temporary result and marker call too.

The selected allocation marker has final symbol PC335784(default/devnet) or
its Pool occurrence listed in binding-map, size8. Its exact step/effect law
is still a small producer; its name or return type is insufficient. The
fallible path's allocation error conversion needs no allocator error-handler
assumption. Prove reachability before bringing any abort/error handler into a
selected prefix. Do not import D189's snapshot allocation-abort wording as a
claim that this explicit `try_reserve_exact` null branch cannot return Err.

Ordered cuts for the fresh caller (scratch writes remain visible to the memory
model even when header is unchanged):

- n=0: construct fresh Vec; compare cap/additional; skip allocator; resize0;
  return the actual empty Vec. No allocation marker or cursor access.
- Checked layout failure: construction/read/check prefix; no marker/shim,
  no ptr/cap commit; map to Core Allocation; execute the actual fresh-Vec drop
  and returned Err. No resize or suffix invented.
- Null: construction/checks/temporary current-memory=None; marker; cursor
  read and failing candidate branch; return null; temporary error stores;
  reserve Err without header commit; map_err/drop/Err. Cursor unchanged.
- Nonnull: same prefix through candidate; cursor store; pointer return;
  temporary success result stores; **ptr field then cap field** commit;
  success branch. Len has no store during reserve. A fault between commits
  retains that exact partial prefix; it is not forced into ordinary Err.
- Abort at any reached primitive: preserve prior history plus executed
  prefix, no returned Vec and no appended normal cleanup. Transaction account
  rollback under P2 does not erase prior oracle observations or justify a
  native allocator frame by itself.

Port22 already proves zero length/empty initialized range from these disjoint
store footprints at modeled cuts. Only after actual field association may that
result be applied to this native header. No equality of helper outputs appears
in any of the above admissions.

## IV. Resize, full value and map_err producer

On reserve Ok, cap=n and len0 imply its second reserve does not grow. For the
actual Accumulator and BatchedWeights bodies this is additionally visible as
one selected finish_grow call followed by initialization, with no second grow.
Connect that observed body to the source instance before claiming the generic
source rule. After identity/field rules, prove the non-growing comparison and
apply the already established arithmetic/frame facts; no additional allocator
certification is required.

Small content rule: interpret `ptr::write`/the emitted memcpy or memset for
one admitted16-byte QM31 or32-byte [u64;4] slot, and source value reads/moves,
with exact footprint and ordered partial failure effects. Actual caller value
QM31::ZERO/[0u64;4] is available here, so source-wide arbitrary Clone equivalence
is unnecessary to close these two zero initializers. The generic `filled`
source still needs its full Clone semantics for arbitrary inputs. Do not
substitute one QM31 coefficient or one u64 limb for the entire value.

Derive a loop invariant: k initialized slots, actual logical len at each
source SetLenOnDrop cut, cap=n, untouched remaining allocation/frame and same
ordered history up to the reached primitive prefix. For n>0, n-1 clones and
one final move; n=0 empty/truncate. LLVM may optimize intermediate logical len
stores away; no claim is made that every source SetLenOnDrop store has a final
machine store. For an abort after k stores, preserve those writes and its
executed control prefix; do not append a successful Vec result. The separate
BatchedWeights conversion/bounds panic remains outside the initialization cut.

Finally interpret literal Result discriminants/move/map_err. Current MIR
already records both exact Allocation closures and branch ordering. Prove
Err skips resize, Ok moves the actual vector, and abnormal exits keep prefix
observations. This is the final composition step, not an admitted whole-helper
output-equivalence or no-oracle field.

## Minimal boundary decision packet, only if a proof route is unavailable

No new trust decision is logically forced by arithmetic: the remaining
operations can instead be proved against an existing sound Rust/SBF memory and
effect semantics. No such selected interpretation is installed by this job,
and zero extraction/backend budget is available here. This packet identifies
the precise possible decision rather than asking for speculative approval.

Possible trusted extension would be **only** the three source/native rules
`load_u64_le : Memory × AdmittedAddress × History -> Outcome (U64 × Memory × History)`,
`store_u64_le : Memory × AdmittedAddress × U64 × History -> Outcome (Memory × History)`,
and `ptr_at : AdmittedArena × U64 -> Option AdmittedPointer`, plus analogous
admitted16/32-byte copy/zero-write rules if the content step is included.
Outcome must distinguish returned/fault/abort and retain prefix history. Entry
addresses/widths/provenance/alignment/frame hypotheses are exactly II–IV,
not a general allocator/Vec/helper contract. Disjointness and private-heap
admission must be proved at the concrete caller, not supplied as output equality.
Do not add these fields without an explicit boundary ruling or an actual proof.

The restricted consumer is the exact shim and caller bodies pinned in
REPORT/binding-map: selected root Rust source hash e56fd181..., actual
heap.rs67153a3f..., verifier.rs8c872d42..., current three full ELF hashes, shim
machine hashes fd8c189f.../9753b555..., and every full LLVM/MIR source hash in
selected-implementation. Full hashes, signatures and actual ranges are stored
there; no name-only association is proposed. **The missing contemporaneous
sysroot/SDK declaration source pin must be supplied before a source-level
extension could be reviewable for adoption.** Current emitted bodies suffice
for an artifact-level review of the narrowly listed operations, not for
claiming the absent declaration identity.

Existing coverage: P7 covers correct reviewed source/locked-dependency to exact
ELF compilation (literal scope in R1-PREMISES-REACCEPTANCE, lines175–190).
P6/AeneasExtraction concerns checked/extracted semantics, not these handwritten
rules; the existing reserve emission remains unconstrained. D157 expressly
excludes unsafe/allocation failure. D189/S2TrustedSdkBorrow/P2 supplies the
stated account association and runtime behavior, not general Vec fields,
initialized contents, source pointer provenance or oracle effects. None is
silently widened by this packet. No new cryptographic assumption is involved.

Supporting evidence: new current artifact hashes, exact fixed-address shim
bodies and store sites, concrete caller initialization and result branches;
reused Port22 unbounded word/body/byte-frame facts and copied finite256-byte
Kani84 check (different native object/sysroot). The latter is diagnostic support
for the allocator shape, **not** evidence that the new primitive rules hold for
deployed SBF. Port22's full axiom audit remains in its own receipts; none ran
again here. No model proof or finite check supplies the missing identity.

What would be trusted: selected typed/native address and memory/effect rules,
including faults, and their association to the named primitive sites. What
would still be proved: arithmetic candidate/branch/frame (already available),
concrete caller admission, cap0 branch choice, len preservation, reserve
success capacity, no second growth, full initialization invariant and error/
abort-prefix composition. No helper equivalence or noHash property is trusted.

Alternatives/cost: (a) recover I1/I2 and prove these finite selected operations
against the project's supported memory/effect semantics, requiring a new
scoped producer and separately authorized extraction/proof budget; (b) prove
these specific machine ranges against a sound SBF interpreter and connect the
required observation transport under P7, requiring selected instruction and
fault/ABI semantics, not whole-SDK certification; (c) accept the narrow rules
as explicit trust after identity recovery and review. No runtime estimate or
new budget is asserted without a supported producer. Rebuilding or repeating
Kani against another sysroot does not discharge I1 or these semantic rules.
