# Early top-level composition review

Pinned inputs: INPUT_REVISIONS.json. Read-only ledger: 96 CLOSED / 125;
29 specifications. No row is closed here. Target not yet established.

## Dependency order and premises

The complete 125-row syntactic call graph is acyclic, including documented
callback edges. DEPENDENCIES.json records the DFS order and empty cycle list.
OwnInit depends on f0 -> f1 -> f6 -> f125 -> f219 -> f318 -> f316 -> f220 ->
f208 -> f15 -> f166 -> f270 -> f361 (with TLS siblings and CLOSED Arc children).
slice:f0 depends on f1 -> f2 -> f4 -> f9 -> f8 -> f6 -> f13 -> f21.
Do not replace this with a theorem whose premise is its own Post.

The absence of graph cycles does NOT establish joint satisfiability of all
representation/machine premises. No nonemptiness theorem for that conjunction
was found in the handoffs. No verified top-level decomposition is claimed.
Provider domains, leaf/native interpretation and source/binary adequacy must
be discharged at actual callers before either composition is usable.

## Checked existing findings retained as SPEC-ERROR

1. **to_vec pending recognizer.** STX session88 proves
   `PV_STX2_ToVecCallPendingDiagnostic.actual_entry_false_pending`: execution11
   is the structured f31 BODY push, but an ignored fallback pending answer
   satisfies the old Pending predicate. New normative Pending requires
   completed=none and programs(callee)=none at the actual consumed reply.
   Old/new and diagnostics are retained in the pinned provider handoff and
   specification archive. This job does not edit that provider.
2. **OwnInit Box codec.** Old decode recognizes bare numeric pairs; the actual
   callback is tagged Box/Unique/NonNull with source references. A premise
   asserting old decode success at14756 is impossible. The frozen spec uses
   `PV_THR2_OwnInitSourceCodec.decodeBridged`, registry-derived data address
   and pinned binary vtable. It requires `allBridged`, not `.all` (thread21').
   W3 history/export helpers do not yet supply the full actual milestone.
3. **Native source-store writes.** W4 D959/D965 identifies five functions at
   eight sites: f9 at f1/487,f15/3756; f10 at f1/930; f93 at f15/3447;
   f167 at f15/3519,3641,4327; f289 at f207/8248. The original interpreter
   cannot perform these writes. OwnInit passes f93 and f289 before its first
   ThreadInit; source7 passes none. The new concrete interpreter is required
   for affected runs. W4's local setter write-definedness and older-reference
   conditions remain derivation obligations, never new Pre/MachineSpec fields.
4. **Counter comparison.** Summary and expanded executions have different
   nextActivation counters (D961 example entry+3 versus entry+8). This is not
   a Rust defect. No library/consumer interface may require that equality.
5. **Entry validity.** Aligned-only or ownership-only slice entry admits
   invalid Rust references (including aligned null). Non-null, alignment and
   typed extent come from entry provenance, with the Foundation builder as the
   existing named caller obligation. Do not assert validity at the copy site.
6. **OwnInit Some premise.** The ledger draft includes Some iteration in Pre.
   The full-strength root spec moves it into the outcome split and also covers
   None/no-box and every earlier stop. This prevents a success-only root.

## Missing proof exports, not specification weakenings

* Most closed native leaves have only argument-reachable-effects/full-reply
  contracts. They do not imply exact values, allocation schedules or purity.
  Their arbitrary Post cannot become the child law. A deterministic environment
  reply plus documented source semantics and an explicit graph adapter are
  required. Every such unsupplied slot is flagged in PLIB_MAP.
* W2 f6 capture/source frame, complete f9/f4; STX full to_vec branch assembly;
  W3 full361/join7 and source/binary bridge adequacy; W4 actual170 machine
  composition; and f6's full loop/transport/return remain unproved.
* W3's name representation/NameOwned must be supplied by Builder270, including
  both Option cases and CString allocation/NUL branches. Scope and Packet Arc
  consumers must use the SAME provider definitions and counts, not a bare
  reference restatement.

No new endpoint premise, T field, success assumption, source edit or row-proof
consumption is introduced. Existing named runtime/compiler/translator and
source/binary obligations are retained. This review reports interface
obstructions; it is not a fresh proof of each provider diagnostic.
