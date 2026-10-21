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
