# Prover commitment part 20 — simulator source isolation

Base `8f5d893d7`; branch `codex/cx-prover-commit20-20261021`.

**Target not yet established.** The failing field-validation loop is isolated
and an owned semantic cone is extracted and checked. Finite table/validator/row
induction and programmed-history composition pass. Universal source transport
and the shipped experiment/WholeRunJoins remain open, as detailed below.

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
external parser/transcript/method declarations. The hash remains a generic
Digest32 parameter; its concrete interior-mutable CoinOracle specialization
and source law are not proved by this extraction. No hash equation is postulated.
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

## Stage 3 — source table gate, history composition, and experiment obstruction

The actual `ProgramOne` empty-entry target now passes. Broad unwind 34
was stopped for shape review (70.135 s, 6367108 KiB, exit 1, swaps 0).
CBMC loop inspection identifies separate tree, allocator and memcmp loops.
The changed harness uses unwind 4 and `memcmp.0:33`, **with unwinding
assertions enabled**. `table-source-empty-v2` passes: exit 0, 18.620 s,
1187524 KiB, swaps 0. It checks the actual BTreeMap/RefCell source call,
returned answer, stored value, one-entry cardinality and unchanged flag for
one arbitrary one-byte address and arbitrary 32-byte answer/initial flag.
This is a bounded source gate, not universal address-length/tree transport.

The overwritten-entry check still grows to the MemoryHigh region. Splitting
value and flag projections, and removing the harness's irrelevant final
map destructor, have not yet supplied an accepted overwrite certificate.
All stopped trials and their exact commands/metrics are retained. No
memory cap is raised; no stopped result is counted as passed or as a
counterexample. The successful pure per-entry collision checks are retained
in their narrower scope. Thus the requested **whole table-source equality
is still open**, despite the finite Lean induction and empty-entry gate.

`ProverCommitTableHistory20` connects the entry/write induction to the
existing `programmedOracle` and `runLog`: arbitrary finite writes, repeated
addresses, common fallback, all adaptive query ordering and early exits.
J8730 passes: exit 0, 1.97 s, 4043548 KiB, swaps 0; standard axioms only.
J8727–8729 are excluded local BEq proof/elaboration failures.

### Why the bounded adapter cannot yet construct the shipped experiment

The source `Coins::nonzero` loops until a nonzero hash answer and increments
a wrapping U64 counter. `ProverCommitNonzero20.search` is a finite unfolding
of the **actual extracted** `sim.coin_owned18`, not an independent-coin
replacement. `zero_prefix` proves every finite unfolding on a single
consistent zero-answer oracle returns no result; `no_uniform_finite_bound`
proves no fixed fuel works for every callback. Its zero token is a parameter,
so the result applies in particular to the zero byte block without kernel
normalization of array-constructor proofs. `empty_observer_no_seed_guess`
checks that a no-query observer has no seed-query exception.

J8726 passes: exit 0, 1.83 s, 4045720 KiB, swaps 0, standard axioms only.
J8722–8725 are excluded local computability/normalization errors; the final
proof uses symbolic array/counter parameters and no new resource options.

**Scope:** this is an obstruction to using a uniformly bounded coordinate
schedule for every source run. It is not a nonexistence theorem for an
ideal WholeRunJoin, does not show that all selectedBad events vanish, does
not calculate the zero-oracle event's probability, and does not establish a
privacy attack. The requested total FSExperiments object needs an explicit
source termination/divergence treatment and its actual coupling/law. Merely
returning an invented abort after an arbitrary coin cap would alter the
source execution. No such cap, abort convention or new bad event is added.

The source cone for the semantic 25 rows is extracted, but source identification
of its owned recursion still needs the iterator/control/caller transport;
the per-chunk Kani result alone is not that theorem. Later rows 25–32,
opening/programming traversal, all source error/retry assembly, and the
shipped randomness/history identification also remain. Existing independent
component proofs are reused at their stated scope, not promoted to these joins.
Consequently **no shippedProverExperiment or ideal/real WholeRunJoin is
claimed**. RustProverRefinement remains unchanged and explicit.

Verbatim new top statements:

```lean
theorem lookup_std (table : List Entry) (query : List UInt8) :
    List.lookup query table = lookup table query

theorem programmed_writes (entries table : List Entry) (collision : Bool)
    (fallback : List UInt8 → OracleAnswer) :
    programmedOracle (writes table collision entries).1 fallback =
      (fun query => (oracleWrites (lookup table) entries query).getD (fallback query))

theorem programmed_writes_history (entries table : List Entry) (collision : Bool)
    (fallback : List UInt8 → OracleAnswer) (program : OProg) (fuel : Nat) :
    runLog program (programmedOracle (writes table collision entries).1 fallback) fuel =
      runLog program (fun query => (oracleWrites (lookup table) entries query).getD (fallback query)) fuel

theorem zero_prefix (zero : Bytes32) (n : Nat) (seed : Bytes32) (attempt : U32) (stream : U8) (counter : U64) :
    search zero (zeroHash zero) seed attempt stream n counter=ok none

theorem no_uniform_finite_bound (zero : Bytes32) (n : Nat) (seed : Bytes32) (attempt : U32) (stream : U8)
    (counter : U64) :
    ¬ (∀ hash : Hash, ∃ result, search zero hash seed attempt stream n counter=ok (some result))

theorem empty_observer_no_seed_guess (seed : R0Z.FsStatement.OracleAnswer) :
    ¬ ProverCommitSeedEvent19.seedGuess [] seed

```

## Final validation and exact changes

J8731 is an excluded audit import omission. Changed audit J8732 includes
the standalone validator import and passes: exact target
`R1Z/ProverCommit20Audit.lean`, exit 0, wall 1.88 s, peak RSS 4100012 KiB,
swaps 0, revision `c3ae4b5fa` plus the exact source snapshot hash. Its 21 full
axioms lines cover every new theorem, both extracted validators, raw checker,
owned row/semantic functions and the retained deployed endpoint. All use
only subsets of `[propext, Classical.choice, Quot.sound]`. This is the one
final changed-cone audit against accepted cached dependencies, not a coherent
frozen release replay. The latter is withheld because source closure remains
open. No unchanged full regression or adversarial/runtime suite was rerun.

Every compiler attempt has exact module, status, wall, RSS, swaps, revision,
source snapshot/hash, dependency fingerprints and axioms/errors in `lean/`.
Attempts J8705–8732 are consumed, including retired pre-launch J8713/J8714;
next available J8733, subject to checking host receipts. Rust receipts pin
commands, source hashes, tools, limits and verdicts separately. Time is in
optimized Charon compilation/translation or Kani symbolic checking, not
unoptimized arithmetic. The host's global Lean lock and required caps are
retained. No SSH session exceeded twenty minutes without output.

No file under `crates/` or `programs/` changed. D129's three frozen ELF
recheck is reused for exactly the unchanged shipped source base; no new ELF
rebuild or artifact equivalence is claimed. Existing P6 boundaries remain;
no new axiom or full-run equality premise is introduced. The deployed endpoint
and RustProverRefinement are byte-identical to base (`endpoint.diff` is empty).
No concurrent-owner module or wallet/key was changed. Nothing is pushed.

The exact proof/reference changes and promotion edits follow. Raw generated
files and hashes are retained separately; unaccepted external templates are
inert `.txt` evidence only.

```diff
diff --git a/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/fields20.rs b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/fields20.rs
new file mode 100644
index 000000000..3231ffcad
--- /dev/null
+++ b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/fields20.rs
@@ -0,0 +1,16 @@
+// Owned state: the consumed byte prefix never borrows across recursion.
+// Short suffixes follow chunks_exact(32): they are not validated.
+#[cfg(any(kani,aeneas_ref))]
+pub mod fields20 {
+    use alloc::vec::Vec;
+    use aspis_core::field::{WideExact,QM31};
+    use super::Error;
+    pub fn validate(row:u8,payload:Vec<u8>,value:usize)->Result<(),Error> {
+        if payload.len()<32 { return Ok(()); }
+        let bytes=&payload[..32];
+        let x=match WideExact::from_le_bytes(bytes) { Some(x)=>x, None=>return Err(Error::NonCanonical {row,value}) };
+        if x.c1()!=QM31::ZERO { return Err(Error::NonCanonical {row,value}); }
+        let tail=payload[32..].to_vec();
+        validate(row,tail,value+1)
+    }
+}
diff --git a/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/semantic20.rs b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/semantic20.rs
new file mode 100644
index 000000000..1969fbfc5
--- /dev/null
+++ b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/semantic20.rs
@@ -0,0 +1,41 @@
+// Fresh owned transcript state for every row. Hash reads still use the
+// unchanged source sample_block_validated; no new hash implementation.
+#[cfg(any(kani,aeneas_ref))]
+pub mod semantic20 {
+    use alloc::vec::Vec;
+    use aspis_core::{Digest32,field::QM31};
+    use super::{Error,SemanticTranscript,row_shape,fields20};
+    pub fn checked(row:u8,record:&[u8])->Result<(),Error> {
+        let (tag,size)=match row_shape(row) {Some(shape)=>shape,None=>return Err(Error::InvalidRow)};
+        if record.len()!=5+size {return Err(Error::Length{row});}
+        if record[0]!=tag {return Err(Error::Tag{row});}
+        if u32::from_le_bytes([record[1],record[2],record[3],record[4]]) as usize !=size {
+            return Err(Error::Length{row});
+        }
+        if row>=14 {
+            match fields20::validate(row,record[5..].to_vec(),0) {Ok(())=>(),Err(e)=>return Err(e)}
+        }
+        Ok(())
+    }
+    pub fn semantic<H:Digest32>(mut state:SemanticTranscript<H>,row:u8,record:Vec<u8>)
+        ->(Result<QM31,Error>,SemanticTranscript<H>) {
+        if row>24 {return (Err(Error::InvalidRow),state);}
+        if row!=state.next_row {
+            return (Err(Error::RowOrder{expected:state.next_row,actual:row}),state);
+        }
+        match checked(row,&record) {Ok(())=>(),Err(e)=>return (Err(e),state)}
+        let block=match state.sample_block_validated(row,&record) {
+            Ok(block)=>block,Err(e)=>return (Err(e),state)
+        };
+        (Ok(crate::sampler::qm31_sample(&block)),state)
+    }
+    pub fn rows<H:Digest32>(state:SemanticTranscript<H>,records:Vec<Vec<u8>>,row:usize,
+        mut sem:[QM31;25])->(Result<[QM31;25],Error>,SemanticTranscript<H>) {
+        if row==25 {return (Ok(sem),state);}
+        let (value,state)=semantic(state,row as u8,records[row].clone());
+        match value {
+            Err(e)=>(Err(e),state),
+            Ok(value)=>{sem[row]=value;rows(state,records,row.wrapping_add(1),sem)}
+        }
+    }
+}
diff --git a/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/table-source20.rs b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/table-source20.rs
new file mode 100644
index 000000000..b6bbeddc8
--- /dev/null
+++ b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/table-source20.rs
@@ -0,0 +1,53 @@
+#[cfg(kani)]
+mod table_source20 {
+    use super::*;
+    #[kani::proof]
+    #[kani::unwind(4)]
+    fn empty_entry() {
+        let address:[u8;1]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
+        let table=RefCell::new((Table::new(),collision));
+        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
+        let (actual,flag)=table.into_inner();
+        assert_eq!(observed,answer);
+        assert_eq!(flag,collision);
+        assert_eq!(actual.get(address.as_slice()),Some(&answer));
+        assert_eq!(actual.len(),1);
+        core::mem::forget(actual);
+    }
+    #[kani::proof]
+    #[kani::unwind(4)]
+    fn overwritten_entry() {
+        let address:[u8;1]=kani::any();let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
+        let mut initial=Table::new();initial.insert(address.to_vec(),old);
+        let table=RefCell::new((initial,collision));
+        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
+        let (actual,flag)=table.into_inner();
+        assert_eq!(observed,answer);
+        assert_eq!(flag,collision || old!=answer);
+        assert_eq!(actual.get(address.as_slice()),Some(&answer));
+        assert_eq!(actual.len(),1);
+        core::mem::forget(actual);
+    }    #[kani::proof]
+    #[kani::unwind(4)]
+    fn overwritten_value() {
+        let address:[u8;1]=kani::any();let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
+        let mut initial=Table::new();initial.insert(address.to_vec(),old);
+        let table=RefCell::new((initial,collision));
+        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
+        let (actual,flag)=table.into_inner();
+        assert_eq!(observed,answer);
+        assert_eq!(actual.get(address.as_slice()),Some(&answer));
+        assert_eq!(actual.len(),1);
+        core::mem::forget(actual);
+    }    #[kani::proof]
+    #[kani::unwind(4)]
+    fn overwritten_flag() {
+        let address:[u8;1]=kani::any();let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();let collision:bool=kani::any();
+        let mut initial=Table::new();initial.insert(address.to_vec(),old);
+        let table=RefCell::new((initial,collision));
+        let observed=ProgramOne{table:&table,answer}.digest(&[&address]);
+        let (actual,flag)=table.into_inner();
+        assert_eq!(flag,collision || old!=answer);
+        core::mem::forget(actual);
+    }
+}
diff --git a/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/table20.rs b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/table20.rs
new file mode 100644
index 000000000..5666fc320
--- /dev/null
+++ b/docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/table20.rs
@@ -0,0 +1,23 @@
+// A per-entry source branch, isolated from allocation/tree traversal.
+// Exactly the ProgramOne post-insert collision update; the previous entry
+// is the return value of Table::insert, which remains a library boundary.
+#[cfg(kani)]
+mod table20 {
+    fn source(previous:Option<[u8;32]>,answer:[u8;32],mut collision:bool)->bool {
+        if let Some(prev)=previous { if prev!=answer {collision=true;} }
+        collision
+    }
+    #[kani::proof]
+    #[kani::unwind(34)]
+    fn hit_entry() {
+        let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
+        let collision:bool=kani::any();
+        assert_eq!(source(Some(old),answer,collision),collision || old!=answer);
+    }
+    #[kani::proof]
+    #[kani::unwind(34)]
+    fn absent_entry() {
+        let answer:[u8;32]=kani::any();let collision:bool=kani::any();
+        assert_eq!(source(None,answer,collision),collision);
+    }
+}
diff --git a/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFields20.lean b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFields20.lean
new file mode 100644
index 000000000..c042979bc
--- /dev/null
+++ b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFields20.lean
@@ -0,0 +1,103 @@
+import AspisR1SimSemantic20.Funs
+/-! The immutable byte operations reuse the parser cone's slice and clone
+proofs (MultiproofConeSlices / MultiproofConeVecLaws), specialized to env J. -/
+set_option autoImplicit false
+namespace R1Z.ProverCommitFields20
+open Aeneas Aeneas.Std Result AspisR1SimSemantic20
+abbrev Bytes := alloc.vec.Vec U8
+
+theorem clone_bytes (s : Slice U8) :
+    alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok s := by
+  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists
+    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (by intros;rfl))
+  exact ho.trans (congrArg (fun v : alloc.vec.Vec U8 => Result.ok v) hv.symm)
+
+theorem drop_total (bytes : Bytes) (bound : 32≤bytes.val.length) :
+    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
+      bytes {start:=32#usize} = ok (Slice.drop bytes 32#usize) := by
+  change core.slice.index.Slice.index _ bytes _ = _
+  simp only [core.slice.index.Slice.index,
+    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
+    show (32#usize).val≤bytes.length from bound,if_true]
+
+def finite (row : U8) (payload : Bytes) (value : Usize) : Nat →
+    Result (core.result.Result Unit r1_wire.Error)
+  | 0 => ok (core.result.Result.Ok ())
+  | n+1 => do
+    if alloc.vec.Vec.len payload < 32#usize then ok (core.result.Result.Ok ())
+    else
+      let bytes ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
+        payload {«end»:=32#usize}
+      let parsed ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
+      match parsed with
+      | none => ok (core.result.Result.Err (r1_wire.Error.NonCanonical row value))
+      | some x => do
+        let q ← aspis_core.field.wide_exact.WideExact.impl.c1 x
+        let bad ← core.cmp.PartialEq.ne.trait_default
+          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q aspis_core.field.QM31.ZERO
+        if bad then ok (core.result.Result.Err (r1_wire.Error.NonCanonical row value))
+        else do
+          let suffix ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
+            payload {start:=32#usize}
+          let tail ← alloc.slice.Slice.to_vec core.clone.CloneU8 suffix
+          finite row tail (Usize.wrapping_add value 1#usize) n
+
+/-- Complete validator recursion for every finite payload, with exact first
+failing field index, ignored short suffix, and errors/divergence of callees. -/
+theorem extracted_finite (remaining : Nat) (row : U8) (payload : Bytes) (value : Usize)
+    (bound : payload.val.length<32*(remaining+1)) :
+    r1_wire.fields20.validate row payload value = finite row payload value remaining := by
+  induction remaining generalizing payload value with
+  | zero =>
+    have short : alloc.vec.Vec.len payload < 32#usize := by change payload.val.length<32;omega
+    rw [r1_wire.fields20.validate]
+    simp only [short,if_true,finite]
+  | succ n ih =>
+    rw [r1_wire.fields20.validate]
+    simp only [finite]
+    by_cases short : alloc.vec.Vec.len payload < 32#usize
+    · simp only [short,if_true]
+    · simp only [short,if_false]
+      have long : 32≤payload.val.length := by change ¬payload.val.length<32 at short;omega
+      have tailEq := drop_total payload long
+      have tailBound : (Slice.drop payload 32#usize).val.length<32*(n+1) := by
+        simp only [Slice.getElem!_val_drop,List.length_drop]
+        change payload.val.length-32<32*(n+1)
+        omega
+      have tailRec := ih (Slice.drop payload 32#usize) (Usize.wrapping_add value 1#usize) tailBound
+      cases hp : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
+          payload {«end»:=32#usize} with
+      | fail e => simp only [bind_tc_fail]
+      | div => simp only [bind_tc_div]
+      | ok bytes =>
+        simp only [bind_tc_ok]
+        cases hd : aspis_core.field.wide_exact.WideExact.from_le_bytes bytes with
+        | fail e => simp only [bind_tc_fail]
+        | div => simp only [bind_tc_div]
+        | ok parsed =>
+          simp only [bind_tc_ok]
+          cases parsed with
+          | none => rfl
+          | some x =>
+            simp only
+            cases hc : aspis_core.field.wide_exact.WideExact.impl.c1 x with
+            | fail e => simp only [bind_tc_fail]
+            | div => simp only [bind_tc_div]
+            | ok q =>
+              simp only [bind_tc_ok]
+              cases he : core.cmp.PartialEq.ne.trait_default
+                aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q aspis_core.field.QM31.ZERO with
+              | fail e => simp only [bind_tc_fail]
+              | div => simp only [bind_tc_div]
+              | ok bad =>
+                simp only [bind_tc_ok]
+                cases bad with
+                | true => rfl
+                | false =>
+                  simp only [Bool.false_eq_true,if_false,tailEq,bind_tc_ok,clone_bytes,lift]
+                  exact tailRec
+
+#print axioms clone_bytes
+#print axioms drop_total
+#print axioms extracted_finite
+end R1Z.ProverCommitFields20
diff --git a/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitNonzero20.lean b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitNonzero20.lean
new file mode 100644
index 000000000..173c68974
--- /dev/null
+++ b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitNonzero20.lean
@@ -0,0 +1,53 @@
+import R1Z.ProverCommitSimulatorCoin18
+import R1Z.ProverCommitSeedEvent19
+/-! A finite-schedule obstruction, not a counterexample to existence of a
+coupling. Coins::nonzero has no source cap; its addresses use a wrapping U64. -/
+set_option autoImplicit false
+noncomputable section
+namespace R1Z.ProverCommitNonzero20
+open Aeneas Aeneas.Std Result ProverCommitSimulatorCoin18
+attribute [local instance] Classical.propDecidable
+
+def zeroHash (zero : Bytes32) : Hash := fun _ => ok zero
+
+def search (zero : Bytes32) (hash : Hash) (seed : Bytes32) (attempt : U32) (stream : U8) :
+    Nat → U64 → Result (Option (Bytes32 × U64))
+  | 0, _ => ok none
+  | n+1, counter => do
+    let (answer,next) ← AspisR1SimulatorCoin18.sim.coin_owned18 hash seed attempt stream counter
+    if answer=zero then search zero hash seed attempt stream n next
+    else ok (some (answer,next))
+
+/-- Any finite unfolding of the actual extracted coin transition can fail to
+supply a nonzero answer. The callback is a single consistent zero oracle. -/
+theorem zero_prefix (zero : Bytes32) (n : Nat) (seed : Bytes32) (attempt : U32) (stream : U8) (counter : U64) :
+    search zero (zeroHash zero) seed attempt stream n counter=ok none := by
+  induction n generalizing counter with
+  | zero => rfl
+  | succ n ih =>
+    simp only [search,extracted_step,zeroHash,bind_tc_ok]
+    change (if zero=zero then
+      search zero (zeroHash zero) seed attempt stream n (U64.wrapping_add counter 1#u64)
+      else ok (some (zero,U64.wrapping_add counter 1#u64))) = ok none
+    rw [if_pos rfl]
+    exact ih _
+
+theorem no_uniform_finite_bound (zero : Bytes32) (n : Nat) (seed : Bytes32) (attempt : U32) (stream : U8)
+    (counter : U64) :
+    ¬ (∀ hash : Hash, ∃ result, search zero hash seed attempt stream n counter=ok (some result)) := by
+  intro all
+  obtain ⟨result,h⟩ := all (zeroHash zero)
+  rw [zero_prefix] at h
+  cases h
+
+/-- No-query observers have no seed-query exception. This does not assert
+that all other selectedBad events vanish, nor refute an entire RunJoin. -/
+theorem empty_observer_no_seed_guess (seed : R0Z.FsStatement.OracleAnswer) :
+    ¬ ProverCommitSeedEvent19.seedGuess [] seed := by
+  rintro ⟨entry,member,_⟩
+  cases member
+
+#print axioms zero_prefix
+#print axioms no_uniform_finite_bound
+#print axioms empty_observer_no_seed_guess
+end R1Z.ProverCommitNonzero20
diff --git a/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitSemantic20.lean b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitSemantic20.lean
new file mode 100644
index 000000000..47e511843
--- /dev/null
+++ b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitSemantic20.lean
@@ -0,0 +1,83 @@
+import AspisR1SimSemantic20.Funs
+set_option autoImplicit false
+namespace R1Z.ProverCommitSemantic20
+open Aeneas Aeneas.Std Result AspisR1SimSemantic20
+abbrev Bytes := alloc.vec.Vec U8
+abbrev Records := alloc.vec.Vec Bytes
+abbrev Values := Array aspis_core.field.QM31 25#usize
+abbrev State (H : Type) := r1_wire.SemanticTranscript H
+abbrev Outcome (H : Type) := Result ((core.result.Result Values r1_wire.Error) × State H)
+
+def finite {H : Type} (hash : aspis_core.digest.Digest32 H) (records : Records)
+    (row : Usize) : Nat → State H → Values → Result ((core.result.Result Values r1_wire.Error) × State H)
+  | 0, state, sem => ok (core.result.Result.Ok sem,state)
+  | n+1, state, sem => do
+    let index ← lift (UScalar.cast .U8 row)
+    let value ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes) records row
+    let record ← alloc.vec.CloneVec.clone core.clone.CloneU8 value
+    let (value,next) ← r1_wire.semantic20.semantic hash state index record
+    match value with
+    | core.result.Result.Err e => ok (core.result.Result.Err e,next)
+    | core.result.Result.Ok value => do
+      let sem ← Array.update sem row value
+      finite hash records (Usize.wrapping_add row 1#usize) n next sem
+
+theorem increment (row : Usize) (bound : row.val<25) :
+    (Usize.wrapping_add row 1#usize).val=row.val+1 := by
+  rw [Usize.wrapping_add_val_eq]
+  have one : (1#usize).val=1 := by scalar_tac
+  rw [one]
+  apply Nat.mod_eq_of_lt
+  have cap := (25#usize).hSize
+  change 25<UScalar.size .Usize at cap
+  omega
+
+/-- Full finite semantic-row execution including errors, advanced state,
+array updates, cloned bytes and the actual three-read hash interface. -/
+theorem extracted_finite {H : Type} (hash : aspis_core.digest.Digest32 H)
+    (records : Records) (row : Usize) (remaining : Nat) (state : State H) (sem : Values)
+    (count : row.val+remaining=25) :
+    r1_wire.semantic20.rows hash state records row sem =
+      finite hash records row remaining state sem := by
+  induction remaining generalizing row state sem with
+  | zero =>
+    have stop : row=25#usize := by scalar_tac
+    rw [r1_wire.semantic20.rows]
+    simp only [stop,if_true,finite]
+  | succ n ih =>
+    have more : row≠25#usize := by scalar_tac
+    rw [r1_wire.semantic20.rows]
+    simp only [more,if_false,finite,lift,bind_tc_ok]
+    cases hi : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes) records row with
+    | fail e => simp only [bind_tc_fail]
+    | div => simp only [bind_tc_div]
+    | ok value =>
+      simp only [bind_tc_ok]
+      cases hc : alloc.vec.CloneVec.clone core.clone.CloneU8 value with
+      | fail e => simp only [bind_tc_fail]
+      | div => simp only [bind_tc_div]
+      | ok record =>
+        simp only [bind_tc_ok]
+        cases hs : r1_wire.semantic20.semantic hash state (UScalar.cast .U8 row) record with
+        | fail e => simp only [bind_tc_fail]
+        | div => simp only [bind_tc_div]
+        | ok result =>
+          rcases result with ⟨value,next⟩
+          simp only [bind_tc_ok,Aeneas.Std.uncurry_apply_pair]
+          cases value with
+          | Err e => rfl
+          | Ok value =>
+            cases hu : Array.update sem row value with
+            | fail e => simp only [hu,bind_tc_fail]
+            | div => simp only [hu,bind_tc_div]
+            | ok after =>
+              simp only [hu,bind_tc_ok,lift]
+              exact ih (Usize.wrapping_add row 1#usize) next after
+                (by rw [increment row (by omega)];omega)
+
+#print axioms increment
+#print axioms extracted_finite
+#print axioms AspisR1SimSemantic20.r1_wire.semantic20.rows
+#print axioms AspisR1SimSemantic20.r1_wire.semantic20.semantic
+#print axioms AspisR1SimSemantic20.r1_wire.fields20.validate
+end R1Z.ProverCommitSemantic20
diff --git a/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTable20.lean b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTable20.lean
new file mode 100644
index 000000000..d446d6b53
--- /dev/null
+++ b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTable20.lean
@@ -0,0 +1,101 @@
+import R1Z.ProverCommitSimulatorInsert19
+/-! Per-entry programming semantics. The source BTreeMap return-value boundary
+and owned Vec/List transport remain distinct from this finite induction. -/
+set_option autoImplicit false
+namespace R1Z.ProverCommitTable20
+variable {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
+abbrev Table (Key Value : Type) := List (Key × Value)
+
+def lookup (table : Table Key Value) (key : Key) : Option Value :=
+  match table with
+  | [] => none
+  | (k,v)::tail => if k=key then some v else lookup tail key
+
+def conflict (old : Option Value) (answer : Value) : Bool :=
+  match old with
+  | none => false
+  | some previous => decide (previous≠answer)
+
+def insert (table : Table Key Value) (key : Key) (answer : Value) (collision : Bool) :
+    Table Key Value × Bool :=
+  match table with
+  | [] => ([(key,answer)],collision)
+  | (k,v)::tail =>
+    if k=key then ((k,answer)::tail,collision || decide (v≠answer))
+    else let out := insert tail key answer collision
+         ((k,v)::out.1,out.2)
+
+/-- The collision branch is needed only for the first matching table entry.
+No key uniqueness assumption is necessary for first-match lookup. -/
+theorem insert_collision (table : Table Key Value) (key : Key) (answer : Value)
+    (collision : Bool) :
+    (insert table key answer collision).2 = (collision || conflict (lookup table key) answer) := by
+  induction table with
+  | nil => simp only [insert,lookup,conflict,Bool.or_false]
+  | cons entry tail ih =>
+    rcases entry with ⟨k,v⟩
+    by_cases same : k=key
+    · simp only [insert,lookup,same,if_true,conflict]
+    · simp only [insert,lookup,same,if_false,ih]
+
+/-- Every individual address gets the overwritten answer or its prior lookup.
+This is a finite entry induction, not an enumeration of keys or byte tables. -/
+theorem insert_lookup (table : Table Key Value) (key query : Key) (answer : Value)
+    (collision : Bool) :
+    lookup (insert table key answer collision).1 query =
+      if key=query then some answer else lookup table query := by
+  induction table with
+  | nil => simp only [insert,lookup]
+  | cons entry tail ih =>
+    rcases entry with ⟨k,v⟩
+    by_cases same : k=key
+    · subst k
+      simp only [insert,if_true,lookup]
+      split_ifs <;> rfl
+    · simp only [insert,same,if_false,lookup,ih]
+      by_cases hit : k=query
+      · have miss : key≠query := by intro h;exact same (hit.trans h.symm)
+        simp only [hit,if_true,miss,if_false]
+      · simp only [hit,if_false]
+
+def writes (table : Table Key Value) (collision : Bool) : List (Key × Value) →
+    Table Key Value × Bool
+  | [] => (table,collision)
+  | (key,answer)::tail =>
+    let next := insert table key answer collision
+    writes next.1 next.2 tail
+
+def oracleWrites (oracle : Key → Option Value) : List (Key × Value) → Key → Option Value
+  | [] => oracle
+  | (key,answer)::tail => oracleWrites (fun query => if key=query then some answer else oracle query) tail
+
+/-- Complete finite write sequence: repeated addresses retain last-write
+semantics. Applying any common fallback preserves every unprogrammed answer. -/
+theorem writes_lookup (entries table : Table Key Value) (collision : Bool) (query : Key) :
+    lookup (writes table collision entries).1 query = oracleWrites (lookup table) entries query := by
+  induction entries generalizing table collision with
+  | nil => rfl
+  | cons entry tail ih =>
+    rcases entry with ⟨key,answer⟩
+    simp only [writes,oracleWrites]
+    rw [ih]
+    have lookupEq : lookup (insert table key answer collision).1 =
+        (fun query => if key=query then some answer else lookup table query) := by
+      funext q
+      exact insert_lookup table key q answer collision
+    rw [lookupEq]
+
+theorem collision_sticky (table : Table Key Value) (entries : Table Key Value) :
+    (writes table true entries).2=true := by
+  induction entries generalizing table with
+  | nil => rfl
+  | cons entry tail ih =>
+    rcases entry with ⟨key,answer⟩
+    simp only [writes,insert_collision,Bool.true_or]
+    exact ih _
+
+#print axioms insert_collision
+#print axioms insert_lookup
+#print axioms writes_lookup
+#print axioms collision_sticky
+end R1Z.ProverCommitTable20
diff --git a/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTableHistory20.lean b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTableHistory20.lean
new file mode 100644
index 000000000..3528213a9
--- /dev/null
+++ b/docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTableHistory20.lean
@@ -0,0 +1,51 @@
+import R1Z.ProverCommitTable20
+import R1Z.ProverCommitJointHistory19
+/-! Finite table writes are connected to the already proved joint adaptive
+history interface. Production BTreeMap and Vec/List transport are separate. -/
+set_option autoImplicit false
+noncomputable section
+namespace R1Z.ProverCommitTableHistory20
+open R0Z.FsStatement R1Z.GamesR1 R1Z.ProverCommitJointHistory19
+open R1Z.ProverCommitTable20
+attribute [local instance] Classical.propDecidable
+abbrev Entry := List UInt8 × OracleAnswer
+
+theorem lookup_std (table : List Entry) (query : List UInt8) :
+    List.lookup query table = lookup table query := by
+  induction table with
+  | nil => rfl
+  | cons entry tail ih =>
+    rcases entry with ⟨key,value⟩
+    simp only [List.lookup_cons,lookup,ih]
+    by_cases same : key=query
+    · subst key
+      simp
+    · have reverse : query≠key := Ne.symm same
+      have different : (query==key)=false := by
+        apply Bool.eq_false_iff.mpr
+        intro equal
+        exact reverse (eq_of_beq equal)
+      simp only [different,same,if_false]
+
+/-- Entire programmed oracle after an arbitrary finite write sequence, with
+one common fallback and last-write semantics even for repeated addresses. -/
+theorem programmed_writes (entries table : List Entry) (collision : Bool)
+    (fallback : List UInt8 → OracleAnswer) :
+    programmedOracle (writes table collision entries).1 fallback =
+      (fun query => (oracleWrites (lookup table) entries query).getD (fallback query)) := by
+  funext query
+  unfold programmedOracle
+  rw [lookup_std,writes_lookup]
+
+/-- Exact adaptive histories, including repeats and early exits. No marginal
+coin substitution or acceptance-only projection is used. -/
+theorem programmed_writes_history (entries table : List Entry) (collision : Bool)
+    (fallback : List UInt8 → OracleAnswer) (program : OProg) (fuel : Nat) :
+    runLog program (programmedOracle (writes table collision entries).1 fallback) fuel =
+      runLog program (fun query => (oracleWrites (lookup table) entries query).getD (fallback query)) fuel := by
+  rw [programmed_writes]
+
+#print axioms lookup_std
+#print axioms programmed_writes
+#print axioms programmed_writes_history
+end R1Z.ProverCommitTableHistory20
```

```diff
--- raw/AspisR1SimFields20/Types.lean
+++ promoted/AspisR1SimFields20/Types.lean
@@ -1,6 +1,8 @@
 -- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
 -- [aspis_r1_cost_probe]: type definitions
-import Aeneas
+import Aeneas.Std
+import Aeneas.Tactic.RustAttributes
+import Aeneas.Data.Discriminant
 open Aeneas Aeneas.Std Result ControlFlow Error
 set_option linter.dupNamespace false
 set_option linter.hashCommand false
@@ -51,7 +53,6 @@
 /-- [aspis_r1_cost_probe::r1_wire::Error]
     Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 24:0-36:1
     Visibility: public -/
-@[discriminant isize]
 inductive r1_wire.Error where
 | Allocation : r1_wire.Error
 | RowOrder : Std.U8 → Std.U8 → r1_wire.Error
@@ -66,4 +67,22 @@
 | Public : r1_wire.Error
 | ActivePole : r1_wire.Error
 
+
+-- Explicit expansion for the pinned Lean 4.32 Aeneas port.
+def r1_wire.Error.read_discriminant : r1_wire.Error → Isize
+  | .Allocation => 0#isize
+  | .RowOrder _ _ => 1#isize
+  | .InvalidRow => 2#isize
+  | .Tag _ => 3#isize
+  | .Length _ => 4#isize
+  | .NonCanonical _ _ => 5#isize
+  | .Boundary _ => 6#isize
+  | .Terminal => 7#isize
+  | .EqualCirclePoints => 8#isize
+  | .TrailingBytes => 9#isize
+  | .Public => 10#isize
+  | .ActivePole => 11#isize
+instance instFields20ErrorDiscriminant : Discriminant r1_wire.Error Isize where
+  read_discriminant := r1_wire.Error.read_discriminant
+
 end AspisR1SimFields20
--- raw/AspisR1SimFields20/Funs.lean
+++ promoted/AspisR1SimFields20/Funs.lean
@@ -1,6 +1,7 @@
 -- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
 -- [aspis_r1_cost_probe]: function definitions
-import Aeneas
+import Aeneas.Std
+import Aeneas.Tactic.RustAttributes
 import AspisR1SimFields20.Types
 open Aeneas Aeneas.Std Result ControlFlow Error
 set_option linter.dupNamespace false
--- raw/AspisR1SimSemantic20/Types.lean
+++ promoted/AspisR1SimSemantic20/Types.lean
@@ -1,6 +1,8 @@
 -- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
 -- [aspis_r1_cost_probe]: type definitions
-import Aeneas
+import Aeneas.Std
+import Aeneas.Tactic.RustAttributes
+import Aeneas.Data.Discriminant
 open Aeneas Aeneas.Std Result ControlFlow Error
 set_option linter.dupNamespace false
 set_option linter.hashCommand false
@@ -61,7 +63,6 @@
 /-- [aspis_r1_cost_probe::r1_wire::Error]
     Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 24:0-36:1
     Visibility: public -/
-@[discriminant isize]
 inductive r1_wire.Error where
 | Allocation : r1_wire.Error
 | RowOrder : Std.U8 → Std.U8 → r1_wire.Error
@@ -84,4 +85,22 @@
   hash : H
   next_row : Std.U8
 
+-- Explicit expansion for the pinned Lean 4.32 Aeneas port.
+def r1_wire.Error.read_discriminant : r1_wire.Error → Isize
+  | .Allocation => 0#isize
+  | .RowOrder _ _ => 1#isize
+  | .InvalidRow => 2#isize
+  | .Tag _ => 3#isize
+  | .Length _ => 4#isize
+  | .NonCanonical _ _ => 5#isize
+  | .Boundary _ => 6#isize
+  | .Terminal => 7#isize
+  | .EqualCirclePoints => 8#isize
+  | .TrailingBytes => 9#isize
+  | .Public => 10#isize
+  | .ActivePole => 11#isize
+instance instSemantic20ErrorDiscriminant : Discriminant r1_wire.Error Isize where
+  read_discriminant := r1_wire.Error.read_discriminant
+
+
 end AspisR1SimSemantic20
--- raw/AspisR1SimSemantic20/Funs.lean
+++ promoted/AspisR1SimSemantic20/Funs.lean
@@ -1,6 +1,7 @@
 -- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
 -- [aspis_r1_cost_probe]: function definitions
-import Aeneas
+import Aeneas.Std
+import Aeneas.Tactic.RustAttributes
 import AspisR1SimSemantic20.Types
 open Aeneas Aeneas.Std Result ControlFlow Error
 set_option linter.dupNamespace false
@@ -421,7 +422,7 @@
   if j > 0#usize
   then
     let j1 ← lift (Std.Usize.wrapping_sub j 1#usize)
-    let i ← lift (Std.U64.wrapping_shl remainder 32#i32)
+    let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
     let i1 ← Array.index_usize rank j1
     let i2 ← lift (core.convert.num.FromU64U32.from i1)
     let dividend ← lift (i ||| i2)
```

### Additional focused runtime validation

`semantic-runtime-v2` runs two **optimized fixture tests**, not a universal
source proof. The source and owned semantic adapters are run with separate
owned state/logs but the same prescribed answer sequence. The tests compare
returned results, final state, next-row value and every ordered concatenated
hash address/answer. They cover all 27 row shapes, wrong-order and invalid-row
guards, truncation, tag/length corruption, every field-error position, the
complete successful 25-row traversal and each possible failing row. Both
pass: exit 0, 5.379 s (including optimized compilation), 355020 KiB, swaps 0,
6G/8G/no-swap/64-task scope. V1 is an excluded test-harness macro-import
compile error (exit 101, 24.867 s, 559576 KiB, swaps 0); V2 imports alloc::vec.
Production function bodies remain unchanged. The launch-time reservation
manifest for V2 and the separate honest post-launch observation of
40.375 GiB populated caps are retained. No fixture is counted as a probability
law or universal source equality; no additional Lean replay was needed.

```diff
--- /dev/null
+++ docs/research/100bit-spend-path-20261013/evidence/prover-commit20-20261021/harness/semantic-tests20.rs
@@ -0,0 +1,60 @@
+#[cfg(all(test,aeneas_ref))]
+mod semantic_tests20 {
+    use super::*;
+    use alloc::vec;
+    use core::cell::RefCell;
+    #[derive(Clone,Copy)]
+    struct TraceHash<'a>(&'a RefCell<Vec<(Vec<u8>,[u8;32])>>);
+    impl Digest32 for TraceHash<'_> {
+        fn digest(&self,parts:&[&[u8]])->[u8;32] {
+            let mut trace=self.0.borrow_mut();
+            let answer=core::array::from_fn(|i| (trace.len() as u8).wrapping_mul(17).wrapping_add(i as u8));
+            let mut address=Vec::new();for part in parts {address.extend_from_slice(part);}
+            trace.push((address,answer));answer
+        }
+    }
+    fn compare(row:u8,next:u8,framed:&[u8]) {
+        let source_log=RefCell::new(Vec::new());let owned_log=RefCell::new(Vec::new());
+        let state=core::array::from_fn(|i|i as u8);
+        let mut source=SemanticTranscript{state,hash:TraceHash(&source_log),next_row:next};
+        let owned=SemanticTranscript{state,hash:TraceHash(&owned_log),next_row:next};
+        let expected=source.semantic(row,framed);
+        let (actual,after)=semantic20::semantic(owned,row,framed.to_vec());
+        assert_eq!(actual,expected);assert_eq!(after.state,source.state);assert_eq!(after.next_row,source.next_row);
+        assert_eq!(*source_log.borrow(),*owned_log.borrow());
+    }
+    #[test]
+    fn all_rows_and_errors() {
+        for row in 0..27 {
+            let (_,size)=row_shape(row).unwrap();let payload=vec![0;size];let frame=record(row,&payload).unwrap();
+            compare(row,row,&frame);compare(row,row.wrapping_add(1),&frame);
+            compare(row,row,&frame[..frame.len()-1]);
+            let mut tag=frame.clone();tag[0]^=128;compare(row,row,&tag);
+            let mut length=frame.clone();length[1]^=1;compare(row,row,&length);
+            if row>=14 {
+                for value in 0..size/32 {
+                    let mut high=frame.clone();high[5+32*value+16]=1;compare(row,row,&high);
+                    let mut noncanonical=frame.clone();noncanonical[5+32*value..9+32*value].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
+                    compare(row,row,&noncanonical);
+                }
+            }
+        }
+        compare(255,255,&[]);
+    }
+    #[test]
+    fn complete_twenty_five_rows() {
+        let records:Vec<Vec<u8>>=(0..25).map(|row|record(row,&vec![0;row_shape(row).unwrap().1]).unwrap()).collect();
+        for fail in 0..=25 {
+            let mut records=records.clone();if fail<25 {records[fail][0]^=128;}
+            let source_log=RefCell::new(Vec::new());let owned_log=RefCell::new(Vec::new());let state=[7;32];
+            let mut source=SemanticTranscript{state,hash:TraceHash(&source_log),next_row:0};
+            let owned=SemanticTranscript{state,hash:TraceHash(&owned_log),next_row:0};
+            let mut expected=[QM31::ZERO;25];let mut error=None;
+            for row in 0..25 {match source.semantic(row as u8,&records[row]) {Ok(x)=>expected[row]=x,Err(e)=>{error=Some(e);break;}}}
+            let (actual,after)=semantic20::rows(owned,records,0,[QM31::ZERO;25]);
+            assert_eq!(actual,match error {None=>Ok(expected),Some(e)=>Err(e)});
+            assert_eq!(after.state,source.state);assert_eq!(after.next_row,source.next_row);
+            assert_eq!(*source_log.borrow(),*owned_log.borrow());
+        }
+    }
+}
```

### Final table obstruction and handoff

The final narrowed source target `sim::table_source20::overwritten_flag`
(`table-source-flag-v1`) **times out**: exit 124, wall 600.191 s, zero swap,
source base `8f5d893d7` with exact instrumented hashes in its input manifest.
Its scope peak is 6601838592 bytes; an observed CBMC RSS is 6427508 KiB at
537 s. GNU time reports 15652 KiB for the wrapper after process-group timeout;
that figure is explicitly **not** the aggregate child peak. Limits remain
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; no higher-cap or
unchanged retry is made. This is a demonstrated verification obstruction,
not a failed mathematical assertion. No task build or SSH process remains.

The exact unchanged-input endpoint diff is empty. No additional assumption,
query loss, bad event, source cap or abort interpretation was introduced.
The new results discharge owned-reference translation and finite schedule /
table-history mathematics; they retain the named source/library/caller and
probability-law obligations. The requested shipped experiment and both
WholeRunJoins are **not established**.

`final-audit.json` checks snapshots/hashes, dependency receipts, every new
theorem audit, all accepted/excluded verdicts, source-prefix/promotion pins,
resource caps, unchanged endpoint/shipped files, and absence of binaries.
`handoff.json` lists the next concrete deliverables. In particular, replace
whole-tree heap exploration with a certified per-key library insertion/lookup
interface, bind expanded rows to the reused compact parser at its caller,
and prove nonzero-loop successful-prefix/no-success treatment with its actual
law before instantiating the bounded history coupling. No release success
or source WholeRunJoin is inferred from the fixture tests.
