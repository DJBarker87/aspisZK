# Prover commitment part 20 — simulator source isolation

Base `8f5d893d7`; branch `codex/cx-prover-commit20-20261021`.

Target not yet established. Work in progress: isolate the transcript/parser
translation failure, split table transport by entry, then assess the concrete
experiment and ideal WholeRunJoin against the actual source definitions.

D129 supplies the accepted three-ELF recheck for the base. No shipped source
has been changed in this stage. Concurrent-owner modules are untouched.

Host workspace reuses compiled part-19 caches. Sources start as hardlinks;
every edited source is detached before writing. Host launcher is forced to
the global Lean lock with 6G/8G/no-swap/64-task caps. Assigned attempts begin
at J8705 after checking existing receipts (last used J8704).

## Stage 1 — failure isolation and per-entry table checks

The full failed cone from part 19 is not retried unchanged. Hiding only
`r1_wire::validate_record_fields` makes the owned semantic-row cone translate
(Charon exit 0, 29.117 s, 579092 KiB; Aeneas exit 0, 0.577 s, 87296 KiB).
Extracting that function alone reproduces `Not_found` (Charon exit 0,
30.080 s, 576212 KiB; Aeneas exit 2, 0.400 s, 71632 KiB). This identifies
the chunks_exact/enumerate field-validation root; the opaque diagnostic is
not promoted. All swaps zero and caps 6G/8G/no-swap/64 tasks.

An owned recursive validator with fresh tail Vec translates (29.793 s,
577476 KiB Charon; 0.871 s, 117744 KiB Aeneas), but its first generated
version has an external `Option::ok_or`. It is excluded; an explicit-match
replacement is in progress. No generated external axiom is accepted.

The previous 600-second whole-tree Kani check is split at the return from
`Table::insert`. Exact source branch and instrumentation hashes are recorded
in `table20-binding.json`. Arbitrary 32-byte old/new values and a sticky flag
pass `hit_entry` (exit 0, 1.998 s, 356852 KiB) and `absent_entry` (exit 0,
1.808 s, 356892 KiB), all swaps zero. No digest or answer law is assumed.
These checks certify the collision branch only: BTreeMap insertion/lookup
and Vec/List correspondence remain explicit source-library boundaries.

`ProverCommitTable20` proves by entry induction the exact first-match
lookup and collision update, then by write induction the complete finite
programming sequence, preserving repeated addresses and last-write semantics.
It requires no key uniqueness assumption and enumerates no address space.
J8705 is an excluded precedence/elaboration error; changed-source J8706
passes (exit 0, 1.32 s, 2532776 KiB, swaps 0). All four printed axioms
are `[propext, Quot.sound]`. Source revision `6bf21f48d` plus exact source
snapshots/dependency fingerprints are in `lean/attempts-8705-8707.jsonl`.
This does not yet discharge the shipped table-source check.

Verbatim new top statements:

```lean
theorem insert_collision (table : Table Key Value) (key : Key) (answer : Value)
    (collision : Bool) :
    (insert table key answer collision).2 = (collision || conflict (lookup table key) answer)

theorem insert_lookup (table : Table Key Value) (key query : Key) (answer : Value)
    (collision : Bool) :
    lookup (insert table key answer collision).1 query =
      if key=query then some answer else lookup table query

theorem writes_lookup (entries table : Table Key Value) (collision : Bool) (query : Key) :
    lookup (writes table collision entries).1 query = oracleWrites (lookup table) entries query

theorem collision_sticky (table : Table Key Value) (entries : Table Key Value) :
    (writes table true entries).2=true

```

## Stage 2 — owned validator and complete semantic rows

The explicit-match validator translates with no external templates. The
owned 25-row cone includes it, row_shape, the exact source
`sample_block_validated`, qm31 sampler and all ordinary errors, with no
opaque parser, transcript, hash-function implementation or method template.
The hash is a generic Digest32 parameter, not a postulated hash equation.
Every row returns its owned transcript state, including semantic errors;
rejected framing never triggers the three transcript reads.

Accepted translation (all exit 0, swaps 0, revision `8f5d893d7` plus exact
host instrumentation/source hashes):

| Target | Wall s | Peak RSS KiB |
|---|---:|---:|
| fields-owned-v2 Charon | 30.301 | 575756 |
| fields-owned-v2 Aeneas | 0.888 | 102608 |
| semantic-owned-v1 Charon | 30.520 | 576616 |
| semantic-owned-v1 Aeneas | 1.193 | 124256 |

Promotion retains raw generated text and exact diffs/hashes. Port edits:
root Aeneas import narrowed to cached Std/RustAttributes; the unavailable
enum attribute expanded to its declaration-order discriminant function and
instance; the source's positive fixed shift count 32 is written as U32
instead of I32 to match the pinned port's wrapping_shl signature. Generated
resource options are unchanged. Initial port failures J8707/J8708/J8712 are
excluded. J8713 did not launch because its dependency had failed; J8714 was
refused by the unchanged-input guard. Both numbers are retired.

J8709/J8710 compile the standalone validator Types/Funs; J8711/J8715 compile
the complete semantic Types/Funs. J8719 proves the entire finite 25-row
schedule, retaining index/clone/update errors and divergent callees:
exit 0, 1.69 s, 2532008 KiB, swaps 0. J8721 proves the validator's finite
schedule for every finite payload without enumerating bytes: exit 0,
1.56 s, 2526804 KiB, swaps 0. New theorem and extracted-function axioms
are all subsets of `[propext, Classical.choice, Quot.sound]`. Failed local
elaboration attempts J8716/J8717/J8718/J8720 are preserved and excluded.
No statement or cap was weakened to repair those errors.

The parser cone's `MultiproofConeSlices.drop_total` and
`MultiproofConeVecLaws` clone proof are reused in specialized env-J form;
the clone call uses this port's `to_vec_spec`. No shared olean is overwritten
except this worker's failed/new module versions, whose snapshots are retained.

One complete 32-byte chunk of the unchanged source validator versus the
owned reference passes Kani for arbitrary bytes and row (2.772 s, 380724 KiB,
exit 0, swaps 0; source feature configuration is in the receipt). The
allocation-heavy variable-length suffix comparison was stopped at 136.332 s,
6382120 KiB, exit 1, swaps 0. Its replacement checks the source's short-input
result without allocating an owned Vec; the Lean validator base case supplies
the reference result. This is a changed gate, not a higher-cap rerun.

### Parser reuse scope

The accepted soundness results are reused unchanged as the compact-wire
specification: `AspisR1.MultiproofConeParserTotal.parse_total` /
`accepted_parse`, strict scanner `scan_total`, and compact `expand_total`.
Their source and existing receipts are under
`100bit-spend-path-20261013/lean/MultiproofCone*.lean` and
`evidence/multiproof-cone-20261021/`. No duplicate compact parser is built.
The simulator walk consumes **logical expanded record frames**, whereas the
compact parser consumes the 57607-byte stored wire and returns expanded
rows. Equality of those two carriers must be installed at the serializer /
parser caller. The new raw-record checker does not silently substitute a
compact parser or claim that caller equality.

Verbatim new top statements:

```lean
theorem increment (row : Usize) (bound : row.val<25) :
    (Usize.wrapping_add row 1#usize).val=row.val+1

theorem extracted_finite {H : Type} (hash : aspis_core.digest.Digest32 H)
    (records : Records) (row : Usize) (remaining : Nat) (state : State H) (sem : Values)
    (count : row.val+remaining=25) :
    r1_wire.semantic20.rows hash state records row sem =
      finite hash records row remaining state sem

theorem clone_bytes (s : Slice U8) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok s

theorem drop_total (bytes : Bytes) (bound : 32≤bytes.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      bytes {start:=32#usize} = ok (Slice.drop bytes 32#usize)

theorem extracted_finite (remaining : Nat) (row : U8) (payload : Bytes) (value : Usize)
    (bound : payload.val.length<32*(remaining+1)) :
    r1_wire.fields20.validate row payload value = finite row payload value remaining

```
