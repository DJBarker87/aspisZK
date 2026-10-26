# Soundness premise ledger — 25 October 2026

**Target not yet established. No premise is discharged by this audit.**

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
| Deduplicated accepted-pair input/continuation families | 82 | 69 | 2 | 40 | 31 | 82 |
| Headline/transport premise families | 0 | 9 | 1 | 9 | 0 | 1 |
| Additional deployment deliverables/trust items | 6 | 30 | 0 | 27 | 3 | 6 |
| All ledger rows (not independent proof gates) | 88 | 108 | 3 | 76 | 34 | 89 |

**Highest-fan-out blocking premise: `firstMarks.source`** (class C, lead; Op5T_ Stage A). It quantifies over every TX1-marked returned event, including rejected child results, and requires the complete successful site layout without a success guard. Under a faithful deployed child trace this conflicts with the wrong-split rejected prefix in `Op5C_RejectedMarks`; the existing `ChildConeJoin.erasure` alone does not force faithful event lists. It gates the shared schedule used by both accepted-pair theorems and their Required14 continuations. This is a source-instance/vacuity obstruction, not a proof that the abstract theorem's arbitrary port type is empty. `secondMarks.source` needs the analogous audit. After that repair, the shared largest deployment gap is the concrete raw canonical source/frozen2 ordered-log join; no measured fan-out count is asserted.

## Reading and counting this ledger

Snapshot: branch `codex/cx-premise-ledger-20261025`, input revision in `input-pins.json`. This ledger supersedes premise counts based only on visible argument counts for these targets. It does not supersede any theorem, security contract or other worker's source. T = accepted external trust; P = implementation/model/instance proof obligation (also explicitly labelled event or budget conditions); C = contradictory or vacuity-suspect source instance. Ownership means accountable cone owner, not a claim that a job has completed the row. Jobs come from retained scratchpad prompts and `design/SOUND-INT-20261025.md`; they may run separately after this snapshot. No live sibling worktree was inspected or edited.

A row is one quantified atomic law family, not one scalar instance: `∀ k<3` and `∀ j:Fin22` stay quantified. Conjunction leaves are split; existential witnesses and all implication guards remain SHARED across their rows. Thus the two Matches leaves must use the SAME successor w′, the four PhysicalRange leaves the SAME start/end, and checkpoint history the SAME key/ledger/events. This is an inventory, not a claim that independently existential leaves are equivalent to the original statement. Payload equalities are not decomposed into byte-by-byte cells. Subtype/vector bounds are carrier well-formedness, not additional security assumptions. Repeated families across the two theorems appear once; distinct TX1/TX2 initial states, two rounds and two batches remain distinct. Data-only record fields are inventoried separately below. Some entry validity facts are definitionally satisfied by Entry.heap or implied by stronger admission fields; they remain listed to expose fields and are not independent open proof gates. Counts are therefore syntactic audit counts, not a security progress percentage.

The two accepted-pair theorems are **different specializations**, not a checked combined theorem:

- op34: `sdkOps adapterOps (Op3I_Install.install (Op4P_Install.install ops)) B claimsStd`.
- TX2: `sdkOps (Tx2I_Install.install adapterOps stageBase finishOps) (Op3I_Install.install ops) B claimsStd`.

`B`, `claimsStd`, the free operation fields, runtime and source association still need concrete instances. The op34 scan conclusion is absent from the TX2 theorem. Installing the union needs a checked same-witness composition; neither result implies that union by name alone.

## Mechanical statements and field expansion

Successful Lean transcripts: [accepted-pair signatures and fields](../evidence/premise-ledger-20261025/Ledger_003/stdout.log), [headline/Port1 signatures and fields](../evidence/premise-ledger-20261025/Ledger_004/stdout.log), [carrier/dictionary fields](../evidence/premise-ledger-20261025/Ledger_005/stdout.log). Helpers use `pp.all false`, `#check @...`, full names and `#print` definitions. Explicit named binder source blocks are retained in `Op4P_Accepted-explicit-binders.lean.txt` and `Tx2I_Accepted-explicit-binders.lean.txt`; together these avoid losing binder names when Lean prints an implication as an arrow. The first two failed diagnostic attempts also preserve maximally explicit notation, but receive no successful-audit credit. There are no new theorem declarations.

All original explicit binders, including the post-existential ones, must be read with the exact retained transcripts. A compact outline of their logical order is:

```
sdk, std, admission1, admission2, extraction, p1, syscall,
accepted1, accepted2, p:Params, port:ChildConeJoin, FirstMarks, SecondMarks
  → ∃ SAME f,s,outer,pre,middle,fs,ss,
      SourceCuts ∧ installed-header[/scan or TX2/finish] ∧ traces/frames/Claims
      ∧ ∀ decode,nodes,y1,
        writer → reader → history → P2Prime → entry → multiproof → scan
          → ∃ parsed, S2CallerFacts ∧ reached-site equivalence
```

TX2's additional finish output is itself universally conditional on `r0`, `r1`, all primitive return equations, `parsed,q,tr,i`, input/read/decode bindings, pairing/matching/semantic/dot/canonicality laws, `saved_ten` and `twelve`. These are group C below. They are not outer premises needed merely to obtain the existential TX2 calls; they ARE still needed to apply the advertised finish/model conclusion. Exported op18/op6/op9/finish successes and SourceCuts are conclusions, never newly counted as assumed cuts. Group B similarly lists premises needed to obtain the Required14 conclusion, not to obtain f,s.

No new top-level typeclass parameter occurs in either accepted-pair signature. Field/Fintype/DecidableEq/Algebra parameters shown in generic PairingLaws/EquationEndpoint definitions are instantiated by the existing concrete model field in this theorem, not unsupplied session A instances. `#print` exposes their generic parameters; actual source/backend correspondence is still group C. The `F` in `finishOps : FinishOps F` is its weights carrier, not a newly assumed Field F. FS2.Params does contain the three separately counted Prop fields, although its p binder is unused here. `root` and `length` also carry no authentication conclusion.

## Common outer antecedents, including hidden fields

| ID / name | Defined at | Meaning | Class | Owner | Removing job / retained boundary | Evidence |
|---|---|---|:---:|---|---|---|
| L001 / `sdk.account_data_cell.data-cell identity` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#account_data_cell` | For related valid local states: data-cell identity | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L002 / `sdk.account_data_cell.lamports-cell identity` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#account_data_cell` | For related valid local states: lamports-cell identity | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L003 / `sdk.account_data_cell.shared data-cell alias agreement` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#account_data_cell` | For related valid local states: shared data-cell alias agreement | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L004 / `sdk.account_data_cell.live data/lamports separation` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#account_data_cell` | For related valid local states: live data/lamports separation | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L005 / `sdk.cell_payload.typed cell payload equality` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#cell_payload` | For related valid local states: typed cell payload equality | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L006 / `sdk.cell_counter.counter equality` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#cell_counter` | For related valid local states: counter equality | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L007 / `sdk.cell_counter.live-guard lookup equality` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#cell_counter` | For related valid local states: live-guard lookup equality | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L008 / `sdk.guard_liveness.live guard identity` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#guard_liveness` | For related valid local states: live guard identity | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L009 / `sdk.guard_liveness.allocation liveness` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#guard_liveness` | For related valid local states: allocation liveness | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L010 / `sdk.guard_liveness.descriptor identity` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#guard_liveness` | For related valid local states: descriptor identity | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L011 / `sdk.shared_ok.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_ok` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L012 / `sdk.shared_ok.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_ok` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L013 / `sdk.shared_err.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_err` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L014 / `sdk.shared_err.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_err` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L015 / `sdk.exclusive_ok.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_ok` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L016 / `sdk.exclusive_ok.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_ok` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L017 / `sdk.exclusive_err.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_err` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L018 / `sdk.exclusive_err.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_err` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L019 / `sdk.shared_deref.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_deref` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L020 / `sdk.shared_deref.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_deref` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L021 / `sdk.exclusive_deref.read.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_deref` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L022 / `sdk.exclusive_deref.read.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_deref` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L023 / `sdk.exclusive_deref.write.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_deref` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L024 / `sdk.exclusive_deref.write.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_deref` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L025 / `sdk.guard_move.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#guard_move` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L026 / `sdk.guard_move.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#guard_move` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L027 / `sdk.shared_drop.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_drop` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L028 / `sdk.shared_drop.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#shared_drop` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L029 / `sdk.exclusive_drop.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_drop` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L030 / `sdk.exclusive_drop.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#exclusive_drop` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L031 / `sdk.error_move_drop.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#error_move_drop` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L032 / `sdk.error_move_drop.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#error_move_drop` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L033 / `sdk.borrow_frame.Matches.reply` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#borrow_frame` | Exact typed transition and reply; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L034 / `sdk.borrow_frame.Matches.related` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#borrow_frame` | Successor library state relates to specified heap; SAME existential w′ in Matches; all original Valid/Enabled/domain guards retained | T | external | Route B adopted; retained library trust | Ledger_003/stdout.log |
| L035 / `std.slice_copy_from_slice` | `docs/research/100bit-spend-path-20261013/lean/S2W_TrustedStd.lean#TrustedStd` | Copy equals the full slice-copy specification, including panic and frame | T | external | TrustedStd retained | Ledger_003/stdout.log |
| L036 / `admission1.entry.valid.uniqueToken` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: pairwise distinct live tokens | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L037 / `admission1.entry.valid.uniqueOwner` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: pairwise distinct live owners | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L038 / `admission1.entry.valid.counterLower` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: minCounter ≤ counter | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L039 / `admission1.entry.valid.counterUpper` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: counter ≤ maxCounter | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L040 / `admission1.entry.valid.counterEquation` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: counter = external + shared count − exclusive count | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L041 / `admission1.entry.valid.exclusive.externalZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: tracked exclusive implies external = 0 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L042 / `admission1.entry.valid.exclusive.sharedZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: tracked exclusive implies no tracked shared guard | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L043 / `admission1.entry.valid.exclusive.one` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: tracked exclusive implies exclusive count = 1 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L044 / `admission1.entry.valid.externalNegative.sharedZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: negative external implies shared count = 0 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L045 / `admission1.entry.valid.externalNegative.exclusiveZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: negative external implies exclusive count = 0 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L046 / `admission1.entry.valid.guardAllocated` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: each live guard has an allocated cell | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L047 / `admission1.entry.valid.guardDescriptor` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: each live guard descriptor equals the payload descriptor | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L048 / `admission1.entry.valid.liveSeparate` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: live account data and lamports cells differ | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L049 / `admission1.entry.valid.liveAllocated` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX1 initial heap: live account data cell is allocated | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L050 / `admission1.entry.freshGuards` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX1: no initial tracked guards | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L051 / `admission1.entry.noExternalBorrows` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX1: external counter is zero | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L052 / `admission1.entry.liveAccount` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX1: all admitted account owners live | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L053 / `admission1.entry.counterZero` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX1: all admitted account counters zero | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L054 / `admission1.entry.sharedCellsOnlyEqualKeys` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX1: shared data cell implies equal keys | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L055 / `admission1.entry.duplicateKeysShareCell` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX1: equal keys imply shared data cell | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L056 / `admission1.related` | `docs/research/100bit-spend-path-20261013/lean/S2W_D189Consolidation.lean#RuntimeEntrypointAdmission` | TX1 concrete library state relates to entry heap | T | external | Runtime interpretation retained | Ledger_003/stdout.log |
| L057 / `admission2.entry.valid.uniqueToken` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: pairwise distinct live tokens | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L058 / `admission2.entry.valid.uniqueOwner` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: pairwise distinct live owners | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L059 / `admission2.entry.valid.counterLower` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: minCounter ≤ counter | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L060 / `admission2.entry.valid.counterUpper` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: counter ≤ maxCounter | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L061 / `admission2.entry.valid.counterEquation` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: counter = external + shared count − exclusive count | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L062 / `admission2.entry.valid.exclusive.externalZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: tracked exclusive implies external = 0 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L063 / `admission2.entry.valid.exclusive.sharedZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: tracked exclusive implies no tracked shared guard | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L064 / `admission2.entry.valid.exclusive.one` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: tracked exclusive implies exclusive count = 1 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L065 / `admission2.entry.valid.externalNegative.sharedZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: negative external implies shared count = 0 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L066 / `admission2.entry.valid.externalNegative.exclusiveZero` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: negative external implies exclusive count = 0 | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L067 / `admission2.entry.valid.guardAllocated` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: each live guard has an allocated cell | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L068 / `admission2.entry.valid.guardDescriptor` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: each live guard descriptor equals the payload descriptor | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L069 / `admission2.entry.valid.liveSeparate` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: live account data and lamports cells differ | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L070 / `admission2.entry.valid.liveAllocated` | `docs/research/100bit-spend-path-20261013/lean/S2TrustedSdkBorrow.lean#Valid` | TX2 initial heap: live account data cell is allocated | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L071 / `admission2.entry.freshGuards` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX2: no initial tracked guards | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L072 / `admission2.entry.noExternalBorrows` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX2: external counter is zero | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L073 / `admission2.entry.liveAccount` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX2: all admitted account owners live | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L074 / `admission2.entry.counterZero` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX2: all admitted account counters zero | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L075 / `admission2.entry.sharedCellsOnlyEqualKeys` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX2: shared data cell implies equal keys | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L076 / `admission2.entry.duplicateKeysShareCell` | `docs/research/100bit-spend-path-20261013/lean/AdapterRwRuntimeAdmission.lean#RuntimeEntrypointAdmission` | TX2: equal keys imply shared data cell | T | external | Runtime/entrypoint admission retained | Ledger_003/stdout.log |
| L077 / `admission2.related` | `docs/research/100bit-spend-path-20261013/lean/S2W_D189Consolidation.lean#RuntimeEntrypointAdmission` | TX2 concrete library state relates to entry heap | T | external | Runtime interpretation retained | Ledger_003/stdout.log |
| L078 / `extraction.stage1` | `docs/research/100bit-spend-path-20261013/lean/S2W_DigestExtraction.lean#AeneasExtraction` | Native TX1 function equals owned extracted stage1 at the exact installed dictionary | T | external | D188 extraction association retained; source-instance pins still required | Ledger_003/stdout.log |
| L079 / `extraction.stage2` | `docs/research/100bit-spend-path-20261013/lean/S2W_DigestExtraction.lean#AeneasExtraction` | Native TX2 function equals owned extracted stage2 at the exact installed dictionary | T | external | D188 extraction association retained; source-instance pins still required | Ledger_003/stdout.log |
| L080 / `extraction.digestSource` | `docs/research/100bit-spend-path-20261013/lean/S2W_DigestExtraction.lean#AeneasExtraction` | op43 equals the emitted digest wrapper around hashv | T | external | D188 extraction association retained; source-instance pins still required | Ledger_003/stdout.log |
| L081 / `p1` | `docs/research/100bit-spend-path-20261013/lean/S2Z_Oracle.lean#P1Realization` | ∀ bytes, sha256 bytes = H bytes, inside the ideal-oracle realization | T | external | Security-contract ROM assumption; no deterministic random-function proof | Ledger_003/stdout.log |
| L082 / `syscall` | `docs/research/100bit-spend-path-20261013/lean/S2Z_Oracle.lean#RuntimeSyscall` | Every successful hashv decodes to sha256 of the exact flattened parts | T | external | Runtime/syscall trust retained | Ledger_003/stdout.log |
| L083 / `accepted1` | `lean/Op4P_Accepted.lean#accepted1; lean/Tx2I_Accepted.lean#accepted1` | TX1 wrapper returns the given inner Ok, post heap and allocator state; event restriction, not a universal-success obligation | P | lead | Preserve as accepted-event antecedent; instantiate from actual run | Ledger_003/stdout.log |
| L084 / `accepted2` | `lean/Op4P_Accepted.lean#accepted2; lean/Tx2I_Accepted.lean#accepted2` | TX2 wrapper returns the given inner Ok, post heap and allocator state; event restriction, not a universal-success obligation | P | lead | Preserve as accepted-event antecedent; instantiate from actual run | Ledger_003/stdout.log |
| L085 / `p.hL` | `docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean#Params` | 34 + D ≤ N; unused p binder in these accepted-pair proofs, not an execution fact | P | lead | No removal job; structural parameter law | Ledger_005/stdout.log |
| L086 / `p.encLen` | `docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean#Params` | every encoded message has length ≤ D; unused p binder in these accepted-pair proofs, not an execution fact | P | lead | No removal job; structural parameter law | Ledger_005/stdout.log |
| L087 / `p.decEnc` | `docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean#Params` | decoder inverts encoder on messages; unused p binder in these accepted-pair proofs, not an execution fact | P | lead | No removal job; structural parameter law | Ledger_005/stdout.log |
| L088 / `port.erasure` | `docs/research/100bit-spend-path-20261013/lean/S2W_ExpandedChildren.lean#ChildConeJoin` | Every typed child execute result erases to invoke ops call, retaining Result failure/divergence behavior | P | lead | Op5T_ batch/marks; S2 child interpreter integration | Ledger_003/stdout.log |
| L089 / `firstMarks.source` | `docs/research/100bit-spend-path-20261013/lean/S2W_TraceSplice.lean#FirstMarks` | ALL events marked TX1 must have the complete firstTrace site layout, with no success guard | C | lead | codex/cx-op5-tx2-20261025, Stage A | ../op5-concrete-20261025/HANDOFF.md |
| L090 / `secondMarks.source` | `docs/research/100bit-spend-path-20261013/lean/S2W_TraceSplice.lean#SecondMarks` | ALL events marked TX2 must have the complete secondTrace layout, with no success guard; analogous rejected-prefix risk, no new contradiction proof here | C | lead | codex/cx-op5-tx2-20261025; audit success conditioning | Ledger_003/stdout.log |

## Shared post-existential Required14 continuation

| ID / name | Defined at | Meaning | Class | Owner | Removing job / retained boundary | Evidence |
|---|---|---|:---:|---|---|---|
| L091 / `writer.header` | `docs/research/100bit-spend-path-20261013/lean/S2W_AuthenticatedInputs.lean#CheckpointWriterConeJoin` | actual successful TX1 checkpoint decodes to both proof/public digests | P | lead | codex/cx-tx1-query-20261025; Q2 writer connection | Ledger_003/stdout.log |
| L092 / `writer.size` | `docs/research/100bit-spend-path-20261013/lean/S2W_AuthenticatedInputs.lean#CheckpointWriterConeJoin` | actual returned checkpoint has length 1768 | P | lead | codex/cx-tx1-query-20261025; Q2 writer connection | Ledger_003/stdout.log |
| L093 / `reader.checkedHeader` | `docs/research/100bit-spend-path-20261013/lean/S2W_AuthenticatedInputs.lean#CheckpointReaderConeJoin` | Actual successful authenticated TX2 checks the same decoded two-digest checkpoint header | P | lead | codex/cx-tx2-query-20261025; Q2 reader connection | Ledger_003/stdout.log |
| L094 / `history.savedAtCommit` | `docs/research/100bit-spend-path-20261013/lean/S2X_RuntimeRetention.lean#CheckpointVersionBinding` | the SAME committed ledger key holds the actual post1 checkpoint bytes | P | lead | S2 lead / RowOrder_AcceptedPairHistory; concrete Pool history instance open | Ledger_003/stdout.log |
| L095 / `history.loadedAtEntry` | `docs/research/100bit-spend-path-20261013/lean/S2X_RuntimeRetention.lean#CheckpointVersionBinding` | TX2 loaded bytes equal the final history value of that SAME key | P | lead | S2 lead / RowOrder_AcceptedPairHistory; concrete Pool history instance open | Ledger_003/stdout.log |
| L096 / `history.noInterveningWrite` | `docs/research/100bit-spend-path-20261013/lean/S2X_RuntimeRetention.lean#CheckpointVersionBinding` | every history event is rollback or writes a different key | P | lead | S2 lead / RowOrder_AcceptedPairHistory; concrete Pool history instance open | Ledger_003/stdout.log |
| L097 / `p2prime.binding.proof` | `docs/research/100bit-spend-path-20261013/lean/R9PoolRuntimeBinding.lean#P2Prime` | For THIS writer/reader pair, both matching digests imply identical complete proof bytes; not hash injectivity | P | lead | S2 lead; protected-history or budgeted collision route, no completed discharge | Ledger_003/stdout.log |
| L098 / `p2prime.binding.pub` | `docs/research/100bit-spend-path-20261013/lean/R9PoolRuntimeBinding.lean#P2Prime` | For THIS writer/reader pair, both matching digests imply identical complete pub bytes; not hash injectivity | P | lead | S2 lead; protected-history or budgeted collision route, no completed discharge | Ledger_003/stdout.log |
| L099 / `entry.parsed` | `docs/research/100bit-spend-path-20261013/lean/S2W_ChildJoins.lean#FirstEntryVerifierConeJoin` | ∃ transcript and parsed proof, parseReached on these SAME proof bytes returns it | P | lead | S2 lead; Op3I_/Op4P_ header/scan insufficient for full parser/transcript instance | Ledger_003/stdout.log |
| L100 / `multiproof.batch0Ranges.PhysicalRange.start` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 0: range starts at slotStart(3*b+k); SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L101 / `multiproof.batch0Ranges.PhysicalRange.finish` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 0: range ends at start + 32*capacity(3*b+k); SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L102 / `multiproof.batch0Ranges.PhysicalRange.bound` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 0: end is within actual proof; SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L103 / `multiproof.batch0Ranges.PhysicalRange.index` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 0: actual checked source range returns nodes b k; SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L104 / `multiproof.batch1Ranges.PhysicalRange.start` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 1: range starts at slotStart(3*b+k); SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L105 / `multiproof.batch1Ranges.PhysicalRange.finish` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 1: range ends at start + 32*capacity(3*b+k); SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L106 / `multiproof.batch1Ranges.PhysicalRange.bound` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 1: end is within actual proof; SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L107 / `multiproof.batch1Ranges.PhysicalRange.index` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#PhysicalRange` | ∀ k < 3, batch 1: actual checked source range returns nodes b k; SAME start/end witnesses across all four rows | P | lead | codex/cx-op5-tx2-20261025 | Ledger_003/stdout.log |
| L108 / `scan.scanArgument.length` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#Y1Range` | actual proof length ≥ 7495 | P | lead | S2 lead; Op4P_ installed scan, internal y1 call connection remains | Ledger_003/stdout.log |
| L109 / `scan.scanArgument.index` | `docs/research/100bit-spend-path-20261013/lean/S2Y_OwnedChildren.lean#Y1Range` | checked [7031,7495) range returns the SAME y1 | P | lead | S2 lead; Op4P_ installed scan, internal y1 call connection remains | Ledger_003/stdout.log |

## TX2 finish continuation, expanded to atomic laws

| ID / name | Defined at | Meaning | Class | Owner | Removing job / retained boundary | Evidence |
|---|---|---|:---:|---|---|---|
| L110 / `r0.field0` | `lean/RowFinish_Control.lean#RoundValues` | Round 0: offset-0 field read returns c0 | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L111 / `r0.field4` | `lean/RowFinish_Control.lean#RoundValues` | Round 0: offset-4 field read returns c4 | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L112 / `r0.add` | `lean/RowFinish_Control.lean#RoundValues` | Round 0: c0+c4 source primitive returns lhs | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L113 / `r0.quarter_run` | `lean/RowFinish_Control.lean#RoundValues` | Round 0: quarter primitive returns quarter | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L114 / `r0.multiply` | `lean/RowFinish_Control.lean#RoundValues` | Round 0: claim times quarter returns rhs | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L115 / `r0.evaluate` | `lean/RowFinish_Control.lean#RoundValues` | Round 0: polynomial primitive returns value at exact alpha | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L116 / `r1.field0` | `lean/RowFinish_Control.lean#RoundValues` | Round 1: offset-0 field read returns c0 | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L117 / `r1.field4` | `lean/RowFinish_Control.lean#RoundValues` | Round 1: offset-4 field read returns c4 | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L118 / `r1.add` | `lean/RowFinish_Control.lean#RoundValues` | Round 1: c0+c4 source primitive returns lhs | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L119 / `r1.quarter_run` | `lean/RowFinish_Control.lean#RoundValues` | Round 1: quarter primitive returns quarter | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L120 / `r1.multiply` | `lean/RowFinish_Control.lean#RoundValues` | Round 1: claim times quarter returns rhs | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L121 / `r1.evaluate` | `lean/RowFinish_Control.lean#RoundValues` | Round 1: polynomial primitive returns value at exact alpha | P | session A | S3/S4/S5/S9 primitive instances; FinT_ consumes unchanged | Ledger_003/stdout.log |
| L122 / `s2` | `lean/Tx2I_Accepted.lean#s2` | actual prepared variant is S2 | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L123 / `ha0` | `lean/Tx2I_Accepted.lean#ha0` | actual alpha[0] read returns alpha0 | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L124 / `ha1` | `lean/Tx2I_Accepted.lean#ha1` | actual alpha[1] read returns alpha1 | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L125 / `hw` | `lean/Tx2I_Accepted.lean#hw` | newWeights returns the SAME weights | P | session A | Session A primitive instance | Ledger_003/stdout.log |
| L126 / `has` | `lean/Tx2I_Accepted.lean#has` | alpha[..2] source slice returns alphas | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L127 / `hp` | `lean/Tx2I_Accepted.lean#hp` | pair primitive returns the SAME pair | P | session A | Session A primitive instance | Ledger_003/stdout.log |
| L128 / `hd` | `lean/Tx2I_Accepted.lean#hd` | dot primitive on actual flushed weights returns dot | P | session A | Session A primitive instance | Ledger_003/stdout.log |
| L129 / `hi` | `lean/Tx2I_Accepted.lean#hi` | stored-decision input on parsed/q/tr returns this i | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L130 / `hq` | `lean/Tx2I_Accepted.lean#hq` | selected transcript queries return this q | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L131 / `read` | `lean/Tx2I_Accepted.lean#read` | literal matching read on these typed rows returns i.data | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L132 / `decoded` | `lean/Tx2I_Accepted.lean#decoded` | query bytes decode to the SAME q | P | lead | Tx2Q_ and S2 same-witness model/transcript connection | Ledger_003/stdout.log |
| L133 / `pairing_S3_S5_S9.round0.boundary` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#RoundLaws` | Round 0: decoded read/add result is the model polynomial boundary | P | session A | S3/S4/S5/S9 laws retained | Ledger_003/stdout.log |
| L134 / `pairing_S3_S5_S9.round0.quarter` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#RoundLaws` | Round 0: decoded multiply is quarter * decoded claim | P | session A | S3/S4/S5/S9 laws retained | Ledger_003/stdout.log |
| L135 / `pairing_S3_S5_S9.round0.eval` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#RoundLaws` | Round 0: decoded polynomial evaluation equals model evaluation | P | session A | S3/S4/S5/S9 laws retained | Ledger_003/stdout.log |
| L136 / `pairing_S3_S5_S9.round1.boundary` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#RoundLaws` | Round 1: decoded read/add result is the model polynomial boundary | P | session A | S3/S4/S5/S9 laws retained | Ledger_003/stdout.log |
| L137 / `pairing_S3_S5_S9.round1.quarter` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#RoundLaws` | Round 1: decoded multiply is quarter * decoded claim | P | session A | S3/S4/S5/S9 laws retained | Ledger_003/stdout.log |
| L138 / `pairing_S3_S5_S9.round1.eval` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#RoundLaws` | Round 1: decoded polynomial evaluation equals model evaluation | P | session A | S3/S4/S5/S9 laws retained | Ledger_003/stdout.log |
| L139 / `pairing_S3_S5_S9.claim` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#PairingLaws` | prepared claim decodes to JointFunctionalBinding.claimedValue | P | session A | S3/S5/S9 instances retained | Ledger_003/stdout.log |
| L140 / `pairing_S3_S5_S9.alpha0` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#PairingLaws` | prepared alpha0 matches data.alpha0 | P | session A | S3/S5/S9 instances retained | Ledger_003/stdout.log |
| L141 / `pairing_S3_S5_S9.alpha1` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#PairingLaws` | prepared alpha1 matches data.alpha1 | P | session A | S3/S5/S9 instances retained | Ledger_003/stdout.log |
| L142 / `pairing_S3_S5_S9.pair` | `docs/research/100bit-spend-path-20261013/lean/Port4D_Pairing.lean#PairingLaws` | source returned pair decodes to exact model dual-fold dot | P | session A | S3/S5/S9 instances retained | Ledger_003/stdout.log |
| L143 / `matches_S4_S7` | `docs/research/100bit-spend-path-20261013/lean/MatchingSupport.lean#match0` | ∀ j : Fin 22, foldWord alpha0 (batchedWord W gamma) (q j) = V(q j) | P | session A | S4/S7 matching arithmetic instance | Ledger_003/stdout.log |
| L144 / `semantic_S3_S9.EquationEndpoint.initial` | `docs/research/100bit-spend-path-20261013/lean/R3SemanticEquationCore.lean#Equations` | first semantic polynomial boundary equals claim; under SAME EquationEndpoint view/claim/polys parsing guards | P | session A | S3/S9 semantic equation instances retained | Ledger_003/stdout.log |
| L145 / `semantic_S3_S9.EquationEndpoint.chain` | `docs/research/100bit-spend-path-20261013/lean/R3SemanticEquationCore.lean#Equations` | ∀ j : Fin 9, next boundary equals previous evaluation at challenge; under SAME EquationEndpoint view/claim/polys parsing guards | P | session A | S3/S9 semantic equation instances retained | Ledger_003/stdout.log |
| L146 / `semantic_S3_S9.EquationEndpoint.terminal` | `docs/research/100bit-spend-path-20261013/lean/R3SemanticEquationCore.lean#Equations` | last semantic evaluation equals exact masked spend terminal; under SAME EquationEndpoint view/claim/polys parsing guards | P | session A | S3/S9 semantic equation instances retained | Ledger_003/stdout.log |
| L147 / `dot_S5` | `lean/Tx2I_Accepted.lean#dot_S5` | Decoded dot equals sum over all64 model final values and actual accumulator weights | P | session A | S5 actual operand instance | Ledger_003/stdout.log |
| L148 / `canonical_S3_S4_S5_S9` | `lean/Tx2I_Accepted.lean#canonical_S3_S4_S5_S9` | sourceE(ofE x)=x for all eight listed round/pair/dot/rhs operands | P | session A | S3/S4/S5/S9 canonicality on actual operands | Ledger_003/stdout.log |
| L149 / `saved_ten` | `lean/Tx2I_Accepted.lean#saved_ten` | Actual op18 resumed accumulator equals model write(model i.data rho q).accumulator | P | lead | codex/cx-tx2-query-20261025; still open | ../tx2-query-20261025/HANDOFF.md |
| L150 / `twelve` | `lean/Tx2I_Accepted.lean#twelve` | Actual op6 return with op9 flushed/back-materialized weights equals twelve model steps from SAME resumed accumulator | P | lead | codex/cx-tx2-query-20261025; still open | ../tx2-query-20261025/HANDOFF.md |
| L151 / `i.data.Functional.map_add` | `docs/research/100bit-spend-path-20261013/lean/MatchingSupport.lean#Functional` | each model F j and F0 preserves addition; structural LinearMap law, already supplied by its model type, not a native-source discharge | P | lead | Model well-formedness; no removal job | Ledger_007/stdout.log |
| L152 / `i.data.Functional.map_smul` | `docs/research/100bit-spend-path-20261013/lean/MatchingSupport.lean#Functional` | each model F j and F0 preserves scalar multiplication; structural LinearMap law, already supplied by its model type, not a native-source discharge | P | lead | Model well-formedness; no removal job | Ledger_007/stdout.log |
| L153 / `tr.statement.initFits` | `docs/research/100bit-spend-path-20261013/lean/R1UnifiedSamplerPublic.lean#Public` | 75 + pubBytes.length ≤ address bound; named proof field of model public carrier, supplied by its type; physical public association remains open | P | lead | Model well-formedness; source bound association in StoredCarrierBinding | Ledger_007/stdout.log |

## Headline and Port1 transport premises

| ID / name | Defined at | Meaning | Class | Owner | Removing job / retained boundary | Evidence |
|---|---|---|:---:|---|---|---|
| L154 / `hqueries` | `docs/research/100bit-spend-path-20261013/lean/OraclePortHeadlineFrozen2PerAttempt.lean#final_soundness` | ∀ ideal H, prover-issued log length ≤ Q; budget condition on the adversary, repeats counted | P | external | Preserve as quantified query-budget condition | Ledger_004/stdout.log |
| L155 / `globalJoin.verifier` | `docs/research/100bit-spend-path-20261013/lean/OraclePortFrozen2Join.lean#AcceptedVerifierJoin` | ∀ H and arbitrary logical Input, source acceptance implies exact eval log+Bool equality; independent logical proof can disagree with physical bytes | C | lead | Port1 canonical carrier corrects domain; original theorem remains conditional | ../ports1-20261023/STAGE4.md |
| L156 / `globalJoin.annotated` | `docs/research/100bit-spend-path-20261013/lean/OraclePortFrozen2Join.lean#AcceptedRunJoin` | For every arbitrary-Input Prover and H, accepted annotated source equals full frozen2 annotated experiment | P | lead | S2 lead; domain correction and per-attempt endpoint composition open | Ledger_004/stdout.log |
| L157 / `canonicalJoin.verifier` | `docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalJoin.lean#AcceptedVerifierJoin` | ∀ byte Submission and H, accepted physical source equals frozen2 eval on input(submission), including ordered oracle answers | P | lead | S2 lead; raw frozen2/source interpretation still open | Ledger_004/stdout.log |
| L158 / `canonicalJoin.annotated` | `docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalJoin.lean#AcceptedRunJoin` | ∀ P whose outputs are Carried in each H, accepted two-pass annotated eval equals frozen2 eval | P | lead | Port1_CanonicalJoin.two_pass reduces to physical + raw join; raw instance open | Ledger_004/stdout.log |
| L159 / `StoredCarrierBinding` | `docs/research/100bit-spend-path-20261013/lean/OraclePortRuntimeBindingC7.lean#StoredCarrierBinding` | ∀ H and accepted runtime run, the ENTIRE run equals annotatedWith D rust (canon P); canonical headline substitutes lift P | P | lead | S2 lead concrete deployment/history/experiment binding; runtime axioms alone insufficient | Ledger_004/stdout.log |
| L160 / `Physical rust (transport predecessor)` | `docs/research/100bit-spend-path-20261013/lean/Port1_StoredCarrier.lean#Physical` | Equal publicBytes and stored bytes imply identical source oracle Programs; driver_physical proves this for its driver, identification with deployed source remains | P | lead | Port1_Driver.rust identification; not an extra endpoint binder | Ledger_004/stdout.log |
| L161 / `Carried.statement` | `docs/research/100bit-spend-path-20261013/lean/Port1_StoredCarrier.lean#Carried` | carried input statement equals input(s).statement; SAME existential s; conditional domain guard inside annotated, already derived for lift/canon/enrich | P | lead | Port1 lift_carried / canon_lift_carried / enrich_carried, reusable established predecessor | Ledger_004/stdout.log |
| L162 / `Carried.stored` | `docs/research/100bit-spend-path-20261013/lean/Port1_StoredCarrier.lean#Carried` | carried stored bytes equal s.stored; SAME existential s; conditional domain guard inside annotated, already derived for lift/canon/enrich | P | lead | Port1 lift_carried / canon_lift_carried / enrich_carried, reusable established predecessor | Ledger_004/stdout.log |
| L163 / `Carried.rows` | `docs/research/100bit-spend-path-20261013/lean/Port1_StoredCarrier.lean#Carried` | every carried proof row has the same erased message as input(s); SAME existential s; conditional domain guard inside annotated, already derived for lift/canon/enrich | P | lead | Port1 lift_carried / canon_lift_carried / enrich_carried, reusable established predecessor | Ledger_004/stdout.log |

## Deployment obligations absent from both accepted-pair theorems

| ID / name | Defined at | Meaning | Class | Owner | Removing job / retained boundary | Evidence |
|---|---|---|:---:|---|---|---|
| L164 / `combine op34 and TX2 installation` | `lean/Op4P_Accepted.lean; lean/Tx2I_Accepted.lean` | Produce ONE checked dictionary/witness chain with both installations, preserving all previous outputs | P | lead | S2 lead / Tx1Q_ / Tx2Q_ | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L165 / `shape full semantic/transcript join` | `lean/Op3I_Accepted.lean` | Header acceptance is not semanticRows27, parseReached or transcript Aligned; connect full parser on SAME bytes | P | lead | S2 lead | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L166 / `batch source Result/effects` | `lean/Op5I_AcceptedBatchCarrierCounterexample.lean` | Install actual batch in TX1 AND TX2; full Result, effects, carrier, rejected-prefix semantics | P | lead | codex/cx-op5-tx2-20261025 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L167 / `indexed authentication` | `docs/research/100bit-spend-path-20261013/lean/Port5Q1_Complete.lean` | Q1 selected indexed openings authenticate to the committed root; root equality alone insufficient | P | lead | codex/cx-op5-tx2-20261025 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L168 / `prepare Context/Data binding` | `docs/research/100bit-spend-path-20261013/lean/Port5Q1_QueryPorts.lean` | Concrete source installation has the SAME model Prepared, transcript, scratch, rho/query context | P | lead | Tx1Q_ / Tx2Q_; SessionAPrepare retained | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L169 / `TX1 ten-step query` | `docs/research/100bit-spend-path-20261013/lean/Port5Q1_Complete.lean` | Bind actual query loop, geometry, reads, all64 weight rows, rhs and power on exact D189 cuts | P | lead | codex/cx-tx1-query-20261025 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L170 / `TX1 flush materialization` | `docs/research/100bit-spend-path-20261013/lean/Port4C_FlushField.lean` | Use actual returned pending state and Vec mutable-back function | P | lead | codex/cx-tx1-query-20261025 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L171 / `TX1 writer/Q2 bridge` | `docs/research/100bit-spend-path-20261013/lean/Port5Q2_Checkpoint.lean` | Prove dictionary bridge, line canonicality, caller/ROM, ObservationBinding, writer admission on SAME Vec | P | lead | codex/cx-tx1-query-20261025 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L172 / `reader native/helper composition` | `docs/research/100bit-spend-path-20261013/lean/Port5Q2_ReaderValidate.lean` | Compose bounded helper substitutions into actual op18, codec/iterator/allocator admission on retained bytes | P | lead | codex/cx-tx2-query-20261025 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L173 / `powers same-return instance` | `docs/research/100bit-spend-path-20261013/lean/Port5Q1_Complete.lean` | Identify resumed gamma and actual whole op17 power array, including no-read effects | P | session A | S1/S3 primitive ownership; Tx2Q_ integration | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L174 / `initial/pending native instance` | `docs/research/100bit-spend-path-20261013/lean/Port3_Constructor.lean` | Installed content constructor theorems need actual Copy/Std/allocator/runtime carrier interpretation | P | lead | S2 lead; Q1 installation integration | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L175 / `finish full effects` | `lean/Tx2I_Finish.lean` | FinT Boolean value equality on actual returned state does not yet transport Result/errors and ordered log | P | lead | FinT_ / Tx2Q_ / S2 interpreter | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L176 / `S6 native decoded/public transport` | `docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledSdk.lean` | Candidate semantic getters and public decoder need native Box/ownership/error/cleanup/adoption correspondence | P | session A | S6 owner; S2 same-call integration | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L177 / `Claims native std slots` | `docs/research/100bit-spend-path-20261013/lean/ClaimsUnrolledFinish.lean` | reserve/intoBox and explicit mapError/boxArray are value models; native ownership/abort/effects not proved | P | lead | S2 lead with S6/Claims owner | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L178 / `remaining primitive instances` | `lean/Tx2I_Accepted.lean` | Instantiate SessionAPrepare/Primitives/Basis/Backends, domain/geometry and nested S3/S4/S5/S9 laws at concrete actual operands | P | session A | Session A; no candidate modified | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L179 / `library/native frame` | `docs/research/100bit-spend-path-20261013/lean/Port1_Library.lean` | Content/library joins need actual native std/runtime/ABI/source dictionary association | P | lead | S2 lead | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L180 / `history protection / Pool-ASQ8` | `docs/research/100bit-spend-path-20261013/lean/S2X_RuntimeRetention.lean` | Construct the SAME protected key/version save/load history; distinguish Pool ASQ8, ASF8 public and1768 verifier CP | P | lead | S2 lead / RowOrder history; no assigned complete concrete instance | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L181 / `oracle model order` | `docs/research/100bit-spend-path-20261013/lean/Port1_ModelOrder.lean` | Compose per-body frozen2 interpreter with exact states, read order, duplicate handling, early exits and rejected oracle prefixes | P | lead | S2 lead; largest shared deployment composition gap | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L182 / `raw canonical join` | `docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalJoin.lean` | Instantiate canonicalJoin.verifier from actual dictionary interpretation, rather than assuming its conclusion | P | lead | S2 lead | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L183 / `two annotation passes` | `docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalJoin.lean` | Apply existing lifting on SAME raw/physical source instance; no new raw all-Input equality | P | lead | S2 lead / Port1 | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L184 / `canonical per-attempt endpoint` | `docs/research/100bit-spend-path-20261013/lean/Port1_CanonicalHeadline.lean` | Compose canonical transport with Frozen2StartChargeProbability and per-attempt Claims: Port1 endpoint currently returns older OraclePortHeadlineFrozen2.Claims | P | lead | S2 lead; no checked canonical-per-attempt composition asserted | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L185 / `deployed stored experiment` | `docs/research/100bit-spend-path-20261013/lean/OraclePortRuntimeBindingC7.lean` | Instantiate full StoredCarrierBinding including runtime accepted run, physical bounds, whole carried data and oracle world | P | lead | S2 lead / external runtime admission | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L186 / `source lowering to frozen ELFs` | `design/SOUND-INT-20261025.md` | Pin native interpreter, source/compiler/features/wire/runtime to the three actual release ELFs; historical pins do not migrate themselves | P | lead | S10 / SBF owner and S2 lead | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L187 / `coherent frozen replay` | `design/SOUND-INT-20261025.md` | One final exact dependency closure replay after focused integration, with target/exit/wall/RSS/swap/revision | P | lead | Release lead; not run by audit | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L188 / `final axioms/trust audit` | `AGENTS.md` | Audit final composed dependency closure and explicit accepted trust list; current cached prints alone are not release audit | P | lead | Release lead; standard-only endpoint audits reused/newly printed | ../sound-int-20261025/manifest.json; design/SOUND-INT-20261025.md |
| L189 / `P7 compiler/LLVM/toolchain` | `design/SOUND-INT-20261025.md` | Accepted compiler/toolchain correctness trust; exact frozen source/artifact association remains proof/integration work | T | external | Accepted external trust retained; pin scope at release | Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md |
| L190 / `P6 Kani association` | `evidence/op4-p6-20261025/P6-EQUIVALENCE.md` | Accepted external Kani/P6 source-step association and its precise scope, not a new Lean axiom | T | external | Accepted external trust retained; pin scope at release | Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md |
| L191 / `runtime allocator/entrypoint/syscall` | `docs/research/100bit-spend-path-20261013/lean/S2W_D189Wrappers.lean` | Accepted Solana runtime, private allocator, abort/rollback and entrypoint semantics; no automatic concrete history instance | T | external | Accepted external trust retained; pin scope at release | Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md |
| L192 / `TrustedStd.option_ok_or` | `docs/research/100bit-spend-path-20261013/lean/Port1_Library.lean#TrustedStd` | ∀ x,e, ops.op0 x e equals emitted okOr; exact Result/error semantics | T | external | Accepted external trust retained; pin scope at release | Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md |
| L193 / `TrustedStd.result_unwrap32` | `docs/research/100bit-spend-path-20261013/lean/Port1_Library.lean#TrustedStd` | ∀ x, ops.unwrap32 x equals emitted unwrap32; failure/panic behavior retained | T | external | Accepted external trust retained; pin scope at release | Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md |
| L194 / `cryptographic security contract` | `docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md` | Ideal-oracle/cryptographic model assumptions in fixed failure game and collision accounting; do not turn source gaps or P2Prime into cryptographic axioms | T | external | Accepted external trust retained; pin scope at release | Ledger_003/receipt.json; ../op4-p6-20261025/HANDOFF.md |
| L195 / `P6Boundary.oracle` | `docs/research/100bit-spend-path-20261013/lean/MultiproofConeP6Frozen2Stage.lean#P6Boundary` | total digest equals ok(rawOracle H input) on every input; stronger than the success-only syscall law; mathematical callback instance, separate from external P6 tool/source association | P | lead | codex/cx-op5-tx2-20261025; source/hash primitive reduction | Ledger_006/stdout.log |
| L196 / `P6Boundary.binary_parent` | `docs/research/100bit-spend-path-20261013/lean/MultiproofConeP6Frozen2Stage.lean#P6Boundary` | ∀ left,right, callback eval is exactly the singleton (parts(left,right),H(parts)) log and H(parts) result; mathematical callback instance, separate from external P6 tool/source association | P | lead | codex/cx-op5-tx2-20261025; source/hash primitive reduction | Ledger_006/stdout.log |
| L197 / `P6Boundary.occupied_parent` | `docs/research/100bit-spend-path-20261013/lean/MultiproofConeP6Frozen2Stage.lean#P6Boundary` | ∀ left,right, occupied callback has exactly the singleton parent-query log and corresponding H result; mathematical callback instance, separate from external P6 tool/source association | P | lead | codex/cx-op5-tx2-20261025; source/hash primitive reduction | Ledger_006/stdout.log |
| L198 / `P6Boundary.sibling_parent` | `docs/research/100bit-spend-path-20261013/lean/MultiproofConeP6Frozen2Stage.lean#P6Boundary` | ∀ left,right, sibling callback has exactly the singleton parent-query log and corresponding H result; mathematical callback instance, separate from external P6 tool/source association | P | lead | codex/cx-op5-tx2-20261025; source/hash primitive reduction | Ledger_006/stdout.log |
| L199 / `P6Boundary.leaf` | `docs/research/100bit-spend-path-20261013/lean/MultiproofConeP6Frozen2Stage.lean#P6Boundary` | ∀ p,q,kind,pos,s with s.n<16, eval of actual leaf equals eval of referenceLeaf, including full Result/state/log; mathematical callback instance, separate from external P6 tool/source association | P | lead | codex/cx-op5-tx2-20261025; source/hash primitive reduction | Ledger_006/stdout.log |

## Data dictionaries are not discharged laws

The complete field inventories are in Ledger_003 and Ledger_005; Ledger_006 expands P6Boundary callback laws and the Port1 library trust fields. They expose what a concrete deployment must identify without treating each arbitrary function value as a proof that it refines the model:

- Library: related, accountData, accountLamports, cellPayload, cellCounter, liveGuard, allocated, run. SDK semantics are exactly the fifteen adopted fields, expanded above; Matches additionally exposes its typed reply and related successor under one witness. Enabled/Fresh guards and Valid are printed. Enabling guards inside a universally guarded library law are not extra unconditional caller hypotheses.
- Allocator: allocate, cleanup. No account-heap effect law is smuggled in: this model gives those operations only their private A state. Admitting the real allocator to this separation is runtime trust plus concrete deployment association.
- Entry: handles, records, buffers, base, provenance. Record: owned account, lamports, rentEpoch. Heap: accounts, ownerLive, allocated, payload, counter, external, guards, ambient. Payload: descriptor/contents; Descriptor: base/length/provenance; Guard: token/cell/owner/kind/descriptor. These are data, with validity laws already expanded in A.
- ChildConeJoin: execute plus erasure. Free execute can manufacture site annotations unless identified with the faithful installed source trace; erasure alone binds only its result. FirstMarks cannot receive source-faithfulness credit from this record.
- B/FinishModel.Boundaries: fromFn, mask, add, mul, terminal, circle, unwrapRoot, claims. ClaimsUnrolledFinish installs its Claims value interpretation; arbitrary B fields are not certified primitive implementations. StdCalls: reserve, intoBox. Native std/ownership/effects obligations are group E.
- `adapterOps : AdapterRw.Ops`, `ops : AspisR1CurrentCaller.Ops`, `stageBase : VTop_Stages.Ops`, `finishOps : AspisR1Stage2.Stage2Finish.FinishOps F`: every field's exact type is printed in Ledger_005. Slot numbering depends on dictionary: current-caller op6 is batch, op7 query, op16 writer, op17 flush, op18 pending, op19 geometry; stage op5 is batch, op6 query, op8 writer, op9 flush, op18 reader, op19 finish. Current-caller op5 is wide_view. `sdkOps`, op3/op4 and TX2 install override selected slots; the remaining source/body installations are group E. No free slot is certified by having a concrete-sounding name.
- Params: D/hL/enc/encLen/dec/decEnc/lbl/σ/iv/rounds. Only hL, encLen and decEnc are Prop fields. Ledger_007 additionally exposes SourceInputs, MatchingSupport.Data/Functional, LinearMap/AddHom, Parsed, erased Prefix, UnifiedSampler.Public, R0P.Public and the generic Field class. The model Functional linearity fields and named public initFits proof are listed in C; they are supplied structurally by their model types. SourceInputs itself has only decoded/data/m31/queryBytes/state31/m32/rho/state32; Data has W/V/F/F0/Y/c0/gamma/kappa/alpha0/alpha1/p0/p1/f. Parsed contains wire/semantic; Prefix contains statement/rounds. No source arithmetic instance follows from these model carriers. RoundValues: six value fields c0,c4,lhs,quarter,rhs,value and six Prop fields per round (group C). CheckpointVersionBinding: key/ledger/events are data witnesses; its three laws are group B. Parsed/q/tr/i, HeaderDecode, nodes and y1 remain explicit quantified carriers; hi/hq/read/decoded bind them only in the conditional finish result.
- Canonical Submission has publicBytes and stored, both arbitrary Bytes. Carried has one SAME Submission witness with exact statement equality, stored equality and erased message equality for every row. Physical is the equality law in D. Decoder is a function to an optional sampler, not a structure containing a hidden source-refinement proof. AcceptedRunJoin has exactly verifier and annotated in each variant, expanded in D. StoredCarrierBinding is the whole accepted-run equality printed in Ledger_004.

Carried's three equalities, listed separately in D, are a domain condition in `canonicalJoin.annotated`, not extra unconditional endpoint assumptions: input/lift/canon/enrich preservation is already proved in Port1. The original endpoint quantifies arbitrary logical Input; the canonical endpoint changes that carrier explicitly. It returns `OraclePortHeadlineFrozen2.Claims`, **not** the newer PerAttempt Claims. The missing corrected canonical per-attempt composition must remain visible. Neither Boolean finish equality nor two annotation passes by themselves identify the deployed experiment.

## Conclusions and release boundary

The requested endpoint's Claims is a conjunction of: accepted extractor mean cost at attempt budget(Q+1161); every returned witness satisfies LiteralProtocol.relation; abort allowance 2^-126+2^-454≤2^-120; failureModel≤totalBound(Q); and, if Q≤Qmax, failureModel≤(Q+1)·2^-100. These are printed CONCLUSIONS, not additional premises. The security contract also requires the explicit repeated/adaptive bound with (Q+34)·B, collision κ(Q+1161), extractor abort and scan exhaustion, including the zero-query corollary; it forbids grinding/work-normalization credit. No deployment or100-bit conclusion is claimed here.

P2Prime is deliberately P. Matching SHA digests do not logically imply byte equality. A protected-history argument or the existing bounded collision-event accounting must justify the concrete source instance; no unconditional injectivity assumption is accepted. Similarly, noInterveningWrite is P even though runtime rollback semantics are T. The authority/permissions/history that protect a specific checkpoint version require proof. Child slot joins, SessionA primitives and source-to-model correspondence are P, never added to the external crypto trust list.

## Validation, freeze and handoff

Seven Lean invocations used out of 15; zero Kani out of 0. Ledger_001 and002 exit1 solely for unsupported `pp.width`; sources/logs retained and excluded. Changed helpers use `format.width`; Ledger_003/004/005/006/007 exit0. No timeout, memory kill, unchanged retry, raised cap, dependency rebuild, package replay, Rust or ELF build. All jobs use unchanged S2W launchers in the task-private host directory, -j1 -M7000, individual MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64 scopes. The admission inspection saw one existing other-worker scope; this task added at most two8GiB scopes, under55GiB. No shared object was overwritten. This is a cached signature audit across two deliberately separate dependency selections, not a coherent combined release replay.

Receipts for every invocation record exact target/command, source hash, source revision anchor, selected dependency/sidecar fingerprint, exit, wall, peak RSS, swap and full axioms lines. `validation-summary.json` records the final helper hashes and reused evidence pins. New successful endpoint prints are exactly [propext, Classical.choice, Quot.sound]; no new theorem or axiom was declared. Revision a8f85a1c67 plus dirty helper hashes identifies the checked inputs. Source revisions and timings from historical proofs are retained in their original receipts, never reassigned to this audit. The field inventory helper has no theorem and therefore no new theorem axioms result (empty print list).


| Attempt / exact target | Exit | Wall seconds | Peak RSS KiB | Swap | Axioms print |
|---|---:|---:|---:|---:|---|
| Ledger_001 / Ledger_Pairs.lean | 1 | 2.051463 | 5135688 | 0 | standard three; failed option diagnostic, excluded |
| Ledger_002 / Ledger_Headlines.lean | 1 | 2.282892 | 4318548 | 0 | standard three; failed option diagnostic, excluded |
| Ledger_003 / Ledger_Pairs.lean | 0 | 1.866120 | 5130492 | 0 | standard three |
| Ledger_004 / Ledger_Headlines.lean | 0 | 1.861589 | 4321676 | 0 | standard three |
| Ledger_005 / Ledger_Carriers.lean | 0 | 1.826442 | 5128336 | 0 | N/A: fields only, no new theorem |
| Ledger_006 / Ledger_Extras.lean | 0 | 1.826796 | 4336768 | 0 | N/A: fields only, no new theorem |
| Ledger_007 / Ledger_ModelCarriers.lean | 0 | 1.892386 | 5130760 | 0 | N/A: fields only, no new theorem |

All seven use source revision anchor `a8f85a1c670e4a3646a5567f460298ebec45612d` plus the exact dirty helper source hashes in their receipts. Successful source hashes match the committed helpers. Original theorem source hashes match their retained successful receipts; the imported PerAttempt object hash also matches its original receipt. This does not certify a full transitive release rebuild.

No assumptions discharged, added, or changed. No existing statement, quantifier, carrier, failure event or metric changed. The ledger identifies source-instance and vacuity risks without repairing them. No shipped/cfg(kani) file, session A candidate, other live worktree, key, protocol parameter, feature or wire format changed. ELF rebuild trigger did not fire. Inherited, NOT freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No binaries/objects/ELFs/archives committed. No push.

Next deliverable: Op5T_'s success-conditioned faithful marks instance and joint non-vacuity, then same-run concrete batch/query/writer/reader installations and the raw canonical ordered-log join. Recount only after comparing the full before/after statements and expanding every new record field. Removing a binder by moving its law into a record or post-existential implication earns no premise-removal credit.

## Uni update — checked union and class C correction, 25 October 2026

The original snapshot and every row above are retained verbatim. This section
updates ONLY L089, L090, L155 and L164 for the corrected Uni path. **Target not
yet established.** See [before/after and witness composition](../evidence/unify-20261025/STAGE-B.md),
[class C and non-vacuity audit](../evidence/unify-20261025/STAGE-C.md), and
[full checked statements/field expansions/axioms](../evidence/unify-20261025/Uni_010/stdout.log).

| Targeted row | Before | After in Uni path | Removal / retained obligation |
|---|---|---|---|
| L089 firstMarks.source | C, unconditional layout even on rejection | P, actual-Rust-Ok guarded Op5T_Marks.FirstMarks | Old universal law removed from the entire accepted-pair chain; faithful SDK child reification remains P |
| L090 secondMarks.source | C, unconditional full TX2 suffix | P, actual-Rust-Ok guarded Op5T_Marks.SecondMarks | Uni_SecondMarks proves successful source sites; Uni_RejectedSecond checks the old faithful-instance contradiction; source-associated child port remains P |
| L155 globalJoin.verifier | C, arbitrary logical proof independent of physical bytes | Retired in corrected downstream endpoint; existing L157 P retained | Uni_CanonicalPerAttempt.no_global_join proves obstruction for any accepting physical verifier; final_soundness uses byte-indexed raw join and returns unchanged per-attempt Claims |
| L164 different specializations | P | Discharged for the checked union dictionary and same witnesses | Uni_Accepted.accepted_pair_unified obtains one f,s,cuts and exports every predecessor conclusion; no compatibility or chosen-cut premise |

Targeted-row delta against the original row universe (NOT a new exhaustive
field recount of every imported Tx1Q/Op5T continuation):

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
| Accepted-pair families, L089/L090 corrected | 82 | 71 | 0 | 40 | 31 | 82 |
| Headline/transport, L155 retired in canonical per-attempt path | 0 | 9 | 0 | 8 | 0 | 1 |
| Additional deliverables, L164 closed | 6 | 29 | 0 | 26 | 3 | 6 |
| Original inventory with ONLY these four deltas | 88 | 109 | 0 | 74 | 34 | 89 |

Arithmetic: C3→0; P108+2 guarded source-instance laws−1 composition gate=109;
L155 is replaced by ALREADY counted L157, not by a new trusted assertion.
Two original rows are retired, hence199→197. This is interface repair plus
one composition closure; it is NOT three proved deployed refinements. Old
L155 remains false for an accepting physical source and is not rehabilitated.
L156 is unchanged historically and is not consumed by the corrected endpoint;
no credit is assigned for it or any other non-targeted row. L157/L159/raw
ordered-log, selected-map/provenance, source-associated child effects,
Session A laws, saved_ten/twelve and native writer adoption remain open.
`WhenBound` is expanded in the audit, not treated as a discharged source law.

Non-vacuity evidence: [source-fixture-audit.json](../evidence/unify-20261025/source-fixture-audit.json)
pins a successful SAME two-transaction LiteSVM fixture at the exact default
ELF f8c0ec72…; all562 admitted source hashes freshly match this worktree.
This reuses retained runtime evidence; no new execution is claimed. Successful
literal source control fixtures and extraction consistency are checked in
Uni_SecondMarks/Uni_Audit. Joint kernel inhabitation of all remaining
runtime/crypto/log/model premises is NOT established. The exact union and
canonical security endpoint remain linked conditionally through the retained
source/runtime/oracle association obligations, rather than an assumed join.

## Recount on Cons_Top (2026-10-25)

**Actual theorem: `AspisR1.Cons_Top.deployed`. Target not yet established.**
Branch `codex/cx-consolidate-20261026`; receipts: `evidence/consolidate-20261026/`.
Date is the actual UTC/UK audit date; the job/branch retains its assigned 20261026 name.

This is a fresh application of Ledger_003–005's method: kernel-print the full
ACTUAL statement, print structures/definitions, split conjunctive law leaves,
keep quantified families and shared existential witnesses/guards, then manually
classify and deduplicate with a reproducible renderer. The classifications are
reviewed audit decisions; Python does not prove implications or discharge rows.
`Cons_039/stdout.log` contains the actual top plus every factored conclusion,
the shared TX2 tuple/calls, and shared Cons_Finish/Cons_Ten outcomes;
`Cons_007` repeats the original field inventory on this coherent selection;
`Cons_008` expands all newly exposed preparation/query/geometry contracts;
`Cons_010` expands canonicality and the remaining data carriers. The initial Cons_006 print hid deep terms; Cons_009 fixed that
display issue for Stage1. Cons_039 freshly audits the final shared-tuple top. Only proof-irrelevant subtype witnesses are hidden.
`Cons_field_catalog.json` mechanically extracts every printed structure field.
The before statement/field evidence and baseline remain Ledger_003–005 and
`premises.json`; the named-binder after sources are `lean/Cons_Top.lean`, `Cons_Result`,
`Cons_Base`, `Cons_Caller`, `Cons_Continuation`, `Cons_Finish` and `Cons_Ten`.

Counting unit remains an atomic law FAMILY, not byte cells or independent
proof gates. Fixed canonicality conjunctions are split into their four/eight
limb laws; Fin22/Fin2/Fin10/Fin4 quantified families are not enumerated. Payload
and whole-vector equalities remain one family. Repeated primitiveOwner,
queryLeaves and Cons_Ten ports refer to the same dictionary and are counted
once. Read/prepare model families repeated in the ten/finish continuations
are deduplicated; existential entry.parsed and the particular ten.parseReached
guard are distinct. Params/Functional/initFits remain structural carrier laws,
not assertions of actual source correctness. No new typeclass is required.
Configuration, FinishOps, query/geometry Ops, B, std, Context and Runtime are
data-only dictionaries/carriers; arbitrary functions are not source proofs.

The old ledger mixed actual antecedents with additional deployment items E
and historical endpoints D. The tables distinguish them. “Deployment alias”
means an umbrella for already counted antecedent leaves; it adds no independent
gate. An absent deployment item is not silently credited as a proof. Counts
measure neither a security percentage nor unconditional release progress.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
| actual antecedent | 82 | 174 | 0 | 26 | 145 | 85 |
| deployment only | 6 | 14 | 0 | 13 | 1 | 6 |
| deployment alias | 0 | 5 | 0 | 4 | 1 | 0 |
| all retained audit rows | 88 | 193 | 0 | 43 | 147 | 91 |
| deduplicated actual plus non-alias deployment | 88 | 188 | 0 | 39 | 146 | 91 |

| Actual antecedent owner | T | P | C |
|---|---:|---:|---:|
| lead | 0 | 26 | 0 |
| session A | 0 | 145 | 0 |
| external | 82 | 3 | 0 |

The expanded P total increases because this theorem EXPOSES previously
uninventoried preparation/primitive and saved-encoding boundaries. This is
not evidence of protocol regression, nor permission to subtract job reports
from the baseline. L149/L150 disappear as inputs, but `tx1_saved` remains a
strong same-Vec/Context/model ten-state equation. A root/state observation is
not that equation. AuS1 removes the authenticated_S1 input by proving a
collision OR indexed-recovery branch under SessionAPrepare. No collision-free
unconditional authentication theorem is claimed.

The same f,s,outer,pre,middle,fs,ss and the same TX1 run supply every native,
writer, preparation-trace and finish output. Fresh first_run is derived from
THAT SourceCuts, not supplied by the caller. Writer admission is reconstructed
on THAT run from immutable prepareOwner and primitiveOwner, not assumed.
Old weaker TX2 finish and TX1 authentication continuations are not exported.
Cons_Ten returns collision OR the ten-state result. Cons_Finish.Outcome retains
AuS1's strongest branch on ONE shared TX2 tuple; Cons_FinishProof derives
saved_ten/twelve internally and retains the original round/pair/dot/semantic
laws. The shared native/finish tuple is constructed once from the accepted source
common call, including Op5T's installed batch. Cons_Base/Caller/Continuation/Result
only factor conclusions; they add no top hypothesis. Native Witness has ten
data fields and no Prop field. The SDK installation equality is a proved output and CPhy is definitionally
the same sdk; complete driver/source Program equality is a proved output.
The headline uses this same installed source/dictionary. It does NOT identify
the arbitrary GExp adversary/project with the accepted native pair; the global
experiment/event/source association remains L157/L159/L181 and the bounds.
Carriers, failure game, Q quantifiers, metric and collision constants are unchanged;
the arbitrary driver/dictionary family is specialized to DrvC's constructed
release installation, explicitly rather than via a compatibility assumption.

### Row-by-row baseline diff

| Baseline | Name | Class / owner | Status | Actual location or reason |
|---|---|---|---|---|
| L001 | sdk.account_data_cell.data-cell identity | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L002 | sdk.account_data_cell.lamports-cell identity | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L003 | sdk.account_data_cell.shared data-cell alias agreement | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L004 | sdk.account_data_cell.live data/lamports separation | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L005 | sdk.cell_payload.typed cell payload equality | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L006 | sdk.cell_counter.counter equality | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L007 | sdk.cell_counter.live-guard lookup equality | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L008 | sdk.guard_liveness.live guard identity | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L009 | sdk.guard_liveness.allocation liveness | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L010 | sdk.guard_liveness.descriptor identity | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L011 | sdk.shared_ok.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L012 | sdk.shared_ok.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L013 | sdk.shared_err.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L014 | sdk.shared_err.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L015 | sdk.exclusive_ok.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L016 | sdk.exclusive_ok.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L017 | sdk.exclusive_err.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L018 | sdk.exclusive_err.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L019 | sdk.shared_deref.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L020 | sdk.shared_deref.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L021 | sdk.exclusive_deref.read.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L022 | sdk.exclusive_deref.read.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L023 | sdk.exclusive_deref.write.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L024 | sdk.exclusive_deref.write.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L025 | sdk.guard_move.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L026 | sdk.guard_move.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L027 | sdk.shared_drop.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L028 | sdk.shared_drop.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L029 | sdk.exclusive_drop.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L030 | sdk.exclusive_drop.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L031 | sdk.error_move_drop.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L032 | sdk.error_move_drop.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L033 | sdk.borrow_frame.Matches.reply | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L034 | sdk.borrow_frame.Matches.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L035 | std.slice_copy_from_slice | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L036 | admission1.entry.valid.uniqueToken | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L037 | admission1.entry.valid.uniqueOwner | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L038 | admission1.entry.valid.counterLower | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L039 | admission1.entry.valid.counterUpper | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L040 | admission1.entry.valid.counterEquation | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L041 | admission1.entry.valid.exclusive.externalZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L042 | admission1.entry.valid.exclusive.sharedZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L043 | admission1.entry.valid.exclusive.one | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L044 | admission1.entry.valid.externalNegative.sharedZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L045 | admission1.entry.valid.externalNegative.exclusiveZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L046 | admission1.entry.valid.guardAllocated | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L047 | admission1.entry.valid.guardDescriptor | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L048 | admission1.entry.valid.liveSeparate | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L049 | admission1.entry.valid.liveAllocated | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L050 | admission1.entry.freshGuards | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L051 | admission1.entry.noExternalBorrows | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L052 | admission1.entry.liveAccount | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L053 | admission1.entry.counterZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L054 | admission1.entry.sharedCellsOnlyEqualKeys | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L055 | admission1.entry.duplicateKeysShareCell | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L056 | admission1.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L057 | admission2.entry.valid.uniqueToken | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L058 | admission2.entry.valid.uniqueOwner | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L059 | admission2.entry.valid.counterLower | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L060 | admission2.entry.valid.counterUpper | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L061 | admission2.entry.valid.counterEquation | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L062 | admission2.entry.valid.exclusive.externalZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L063 | admission2.entry.valid.exclusive.sharedZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L064 | admission2.entry.valid.exclusive.one | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L065 | admission2.entry.valid.externalNegative.sharedZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L066 | admission2.entry.valid.externalNegative.exclusiveZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L067 | admission2.entry.valid.guardAllocated | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L068 | admission2.entry.valid.guardDescriptor | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L069 | admission2.entry.valid.liveSeparate | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L070 | admission2.entry.valid.liveAllocated | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L071 | admission2.entry.freshGuards | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L072 | admission2.entry.noExternalBorrows | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L073 | admission2.entry.liveAccount | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L074 | admission2.entry.counterZero | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L075 | admission2.entry.sharedCellsOnlyEqualKeys | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L076 | admission2.entry.duplicateKeysShareCell | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L077 | admission2.related | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L078 | extraction.stage1 | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L079 | extraction.stage2 | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L080 | extraction.digestSource | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L081 | p1 | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L082 | syscall | T / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L083 | accepted1 | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L084 | accepted2 | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L085 | p.hL | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L086 | p.encLen | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L087 | p.decEnc | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L088 | port.erasure | P / lead | removed (derived/superseded) | Constructed SdkD child port; erasure is a theorem, not a supplied ChildConeJoin. |
| L089 | firstMarks.source | C / lead | removed (derived/superseded) | Old unguarded FirstMarks is not a premise; success-conditioned concrete marks consumed internally. |
| L090 | secondMarks.source | C / lead | removed (derived/superseded) | Old unguarded SecondMarks is not a premise; concrete marks consumed internally. |
| L091 | writer.header | P / lead | removed (derived/superseded) | Writer.header is derived and exported on the exact cut. |
| L092 | writer.size | P / lead | removed (derived/superseded) | Writer.size is derived and exported. |
| L093 | reader.checkedHeader | P / lead | removed (derived/superseded) | Reader.checkedHeader is derived and exported. |
| L094 | history.savedAtCommit | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L095 | history.loadedAtEntry | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L096 | history.noInterveningWrite | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L097 | p2prime.binding.proof | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L098 | p2prime.binding.pub | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L099 | entry.parsed | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L100 | multiproof.batch0Ranges.PhysicalRange.start | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L101 | multiproof.batch0Ranges.PhysicalRange.finish | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L102 | multiproof.batch0Ranges.PhysicalRange.bound | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L103 | multiproof.batch0Ranges.PhysicalRange.index | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L104 | multiproof.batch1Ranges.PhysicalRange.start | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L105 | multiproof.batch1Ranges.PhysicalRange.finish | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L106 | multiproof.batch1Ranges.PhysicalRange.bound | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L107 | multiproof.batch1Ranges.PhysicalRange.index | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L108 | scan.scanArgument.length | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L109 | scan.scanArgument.index | P / lead | removed (derived/superseded) | Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise. |
| L110 | r0.field0 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L111 | r0.field4 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L112 | r0.add | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L113 | r0.quarter_run | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L114 | r0.multiply | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L115 | r0.evaluate | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L116 | r1.field0 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L117 | r1.field4 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L118 | r1.add | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L119 | r1.quarter_run | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L120 | r1.multiply | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L121 | r1.evaluate | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L122 | s2 | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L123 | ha0 | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L124 | ha1 | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L125 | hw | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L126 | has | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L127 | hp | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L128 | hd | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L129 | hi | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L130 | hq | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L131 | read | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L132 | decoded | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L133 | pairing_S3_S5_S9.round0.boundary | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L134 | pairing_S3_S5_S9.round0.quarter | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L135 | pairing_S3_S5_S9.round0.eval | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L136 | pairing_S3_S5_S9.round1.boundary | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L137 | pairing_S3_S5_S9.round1.quarter | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L138 | pairing_S3_S5_S9.round1.eval | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L139 | pairing_S3_S5_S9.claim | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L140 | pairing_S3_S5_S9.alpha0 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L141 | pairing_S3_S5_S9.alpha1 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L142 | pairing_S3_S5_S9.pair | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L143 | matches_S4_S7 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L144 | semantic_S3_S9.EquationEndpoint.initial | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L145 | semantic_S3_S9.EquationEndpoint.chain | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L146 | semantic_S3_S9.EquationEndpoint.terminal | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L147 | dot_S5 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L148 | canonical_S3_S4_S5_S9 | P / session A | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L149 | saved_ten | P / lead | removed (derived/superseded) | No saved_ten input in the sole finish branch; derived internally from same saved encoding and reader success. See retained tx1_saved. |
| L150 | twelve | P / lead | removed (derived/superseded) | No twelve input in the sole finish branch; derived by Tx2N under primitive/geometry/read/preparation laws. |
| L151 | i.data.Functional.map_add | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L152 | i.data.Functional.map_smul | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L153 | tr.statement.initFits | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L154 | hqueries | P / external | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L155 | globalJoin.verifier | C / lead | removed (derived/superseded) | Superseded arbitrary-logical-input domain, not proof of that contradictory/global statement. |
| L156 | globalJoin.annotated | P / lead | removed (derived/superseded) | Superseded unrestricted annotated interface; canonical domain used instead. |
| L157 | canonicalJoin.verifier | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L158 | canonicalJoin.annotated | P / lead | removed (derived/superseded) | Derived two-pass canonical annotation from raw verifier join and constructed Physical. |
| L159 | StoredCarrierBinding | P / lead | still present (actual antecedent) | Literal expanded antecedent, at the constructed installed instance. |
| L160 | Physical rust (transport predecessor) | P / lead | removed (derived/superseded) | Constructed implementation/source and proved Program equality on all inputs; SDK identities checked, not assumed. |
| L161 | Carried.statement | P / lead | removed (derived/superseded) | Carried.statement is derived for canon(lift P); no independent Carried hypothesis. |
| L162 | Carried.stored | P / lead | removed (derived/superseded) | Carried.stored is derived for canon(lift P). |
| L163 | Carried.rows | P / lead | removed (derived/superseded) | Carried.rows is derived for canon(lift P). |
| L164 | combine op34 and TX2 installation | P / lead | removed (derived/superseded) | One checked CPhy/T2Nat/AuS1 dictionary and shared f,s/run construction. |
| L165 | shape full semantic/transcript join | P / lead | still present (deployment only) | Header/shape value installed; full source semantic/transcript association remains in L129-L132 and raw join. |
| L166 | batch source Result/effects | P / lead | still present (deployment only) | Installed source batch effects are identified by driver construction; native lowering/adoption/effect association still required. |
| L167 | indexed authentication | P / lead | removed (derived/superseded) | Indexed authentication is derived with a collision alternative on the same trace; no authenticated_S1 input. SessionAPrepare remains. |
| L168 | prepare Context/Data binding | P / lead | still present (deployment only) | Same Context/data/preparation and saved-byte association remains as N preparation laws and tx1_saved; not discharged by state arithmetic. |
| L169 | TX1 ten-step query | P / lead | removed (derived/superseded) | Native ten-step query instance and collision-or-model ten state on the same run; preparation/read/geometry leaves remain. |
| L170 | TX1 flush materialization | P / lead | removed (derived/superseded) | Native flush materialization on the same run. |
| L171 | TX1 writer/Q2 bridge | P / lead | removed (derived/superseded) | Actual writer and native-writer results derived on same run; full Context/physical encoding still tx1_saved. |
| L172 | reader native/helper composition | P / lead | removed (derived/superseded) | Native reader/OnRun/helper composition exported; no native-reader equality hypothesis. |
| L173 | powers same-return instance | P / session A | removed (derived/superseded) | Installed same-return powers uses Tx2N_Powers and existing checked early_powers, no new powers hypothesis. |
| L174 | initial/pending native instance | P / lead | removed (derived/superseded) | Installed initial/pending constructor derived on the exact run. |
| L175 | finish full effects | P / lead | removed (derived/superseded) | Complete successful finish silent-effects law exported; session A pairing/dot/round laws retained. |
| L176 | S6 native decoded/public transport | P / session A | still present (deployment only) | Semantic source getters/cuts compose, but native ownership/error/cleanup/adoption remains outside the kernel statement. |
| L177 | Claims native std slots | P / lead | still present (deployment only) | Arbitrary Claims reserve/intoBox data dictionary has no full native ownership/abort/effects interpretation. |
| L178 | remaining primitive instances | P / session A | still present (deployment only) | Covered explicitly by N001-N114 primitive/preparation law leaves; do not add another count for this umbrella. |
| L179 | library/native frame | P / lead | still present (deployment only) | SDK borrow trust retained; concrete allocator/library/native frame and source association remain deployment obligations. |
| L180 | history protection / Pool-ASQ8 | P / lead | still present (deployment only) | Specific cross-transaction history protection remains L094-L096; runtime rollback semantics alone is insufficient. |
| L181 | oracle model order | P / lead | still present (deployment only) | Complete source Program equality is proved; ordered source-to-frozen2 model event/projection association remains raw L157/GExq work. |
| L182 | raw canonical join | P / lead | still present (deployment only) | Same obligation as literal L157 at this installed source, not a second independent gate. |
| L183 | two annotation passes | P / lead | removed (derived/superseded) | Two canonical annotation passes derived from raw verifier join and Physical. |
| L184 | canonical per-attempt endpoint | P / lead | removed (derived/superseded) | Corrected canonical PerAttempt Claims and repeated/adaptive bound plus zero-query corollary proved conditionally. |
| L185 | deployed stored experiment | P / lead | still present (deployment only) | Same obligation as literal L159 at this installed source, not a second independent gate. |
| L186 | source lowering to frozen ELFs | P / lead | still present (deployment only) | Source-to-SBF/artifact association for the exact frozen ELFs remains; no new binary proof. |
| L187 | coherent frozen replay | P / lead | still present (deployment only) | Only coherent cached focused composition audited; full frozen dependency release replay not run. |
| L188 | final axioms/trust audit | P / lead | still present (deployment only) | Current top standard-axiom audit passes; final release dependency/trust/adoption audit remains. |
| L189 | P7 compiler/LLVM/toolchain | T / external | still present (deployment only) | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L190 | P6 Kani association | T / external | still present (deployment only) | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L191 | runtime allocator/entrypoint/syscall | T / external | still present (deployment only) | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L192 | TrustedStd.option_ok_or | T / external | still present (deployment only) | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L193 | TrustedStd.result_unwrap32 | T / external | still present (deployment only) | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L194 | cryptographic security contract | T / external | still present (deployment only) | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L195 | P6Boundary.oracle | P / lead | still present (deployment only) | Actual native total-oracle/source association remains, distinct from success-only RuntimeSyscall; no P6-boundary binder in this top. |
| L196 | P6Boundary.binary_parent | P / lead | still present (deployment only) | Actual native binary-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L197 | P6Boundary.occupied_parent | P / lead | still present (deployment only) | Actual native occupied-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L198 | P6Boundary.sibling_parent | P / lead | still present (deployment only) | Actual native sibling-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L199 | P6Boundary.leaf | P / lead | still present (deployment only) | Actual native leaf callback/source association remains a deployment obligation; no leaf gate binder here. |

### Newly present expanded antecedents

Every row below is P. This includes the replacement boundaries behind the
reported removals; these are not new external cryptographic assumptions.

| ID | Law family | Owner | Meaning | Blocker |
|---|---|---|---|---|
| N001 | prepareOwner.accepted.variant | session A | Every successful actual preparation has variant S2; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N002 | prepareOwner.accepted.queries | session A | Every successful actual preparation has all 22 query words below 262144; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N003 | prepareOwner.accepted.gamma.c0.c0.a | session A | Every successful actual preparation has gamma limb c0.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N004 | prepareOwner.accepted.gamma.c0.c0.b | session A | Every successful actual preparation has gamma limb c0.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N005 | prepareOwner.accepted.gamma.c0.c1.a | session A | Every successful actual preparation has gamma limb c0.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N006 | prepareOwner.accepted.gamma.c0.c1.b | session A | Every successful actual preparation has gamma limb c0.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N007 | prepareOwner.accepted.gamma.c1.c0.a | session A | Every successful actual preparation has gamma limb c1.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N008 | prepareOwner.accepted.gamma.c1.c0.b | session A | Every successful actual preparation has gamma limb c1.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N009 | prepareOwner.accepted.gamma.c1.c1.a | session A | Every successful actual preparation has gamma limb c1.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N010 | prepareOwner.accepted.gamma.c1.c1.b | session A | Every successful actual preparation has gamma limb c1.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N011 | prepareOwner.accepted.kappa.c0.c0.a | session A | Every successful actual preparation has kappa limb c0.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N012 | prepareOwner.accepted.kappa.c0.c0.b | session A | Every successful actual preparation has kappa limb c0.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N013 | prepareOwner.accepted.kappa.c0.c1.a | session A | Every successful actual preparation has kappa limb c0.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N014 | prepareOwner.accepted.kappa.c0.c1.b | session A | Every successful actual preparation has kappa limb c0.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N015 | prepareOwner.accepted.kappa.c1.c0.a | session A | Every successful actual preparation has kappa limb c1.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N016 | prepareOwner.accepted.kappa.c1.c0.b | session A | Every successful actual preparation has kappa limb c1.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N017 | prepareOwner.accepted.kappa.c1.c1.a | session A | Every successful actual preparation has kappa limb c1.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N018 | prepareOwner.accepted.kappa.c1.c1.b | session A | Every successful actual preparation has kappa limb c1.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N019 | prepareOwner.accepted.alpha.c0.c0.a | session A | Every successful actual preparation has alpha limb c0.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N020 | prepareOwner.accepted.alpha.c0.c0.b | session A | Every successful actual preparation has alpha limb c0.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N021 | prepareOwner.accepted.alpha.c0.c1.a | session A | Every successful actual preparation has alpha limb c0.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N022 | prepareOwner.accepted.alpha.c0.c1.b | session A | Every successful actual preparation has alpha limb c0.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N023 | prepareOwner.accepted.alpha.c1.c0.a | session A | Every successful actual preparation has alpha limb c1.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N024 | prepareOwner.accepted.alpha.c1.c0.b | session A | Every successful actual preparation has alpha limb c1.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N025 | prepareOwner.accepted.alpha.c1.c1.a | session A | Every successful actual preparation has alpha limb c1.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N026 | prepareOwner.accepted.alpha.c1.c1.b | session A | Every successful actual preparation has alpha limb c1.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N027 | prepareOwner.accepted.rho.c0.a | session A | Every successful actual preparation has rho limb c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N028 | prepareOwner.accepted.rho.c0.b | session A | Every successful actual preparation has rho limb c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N029 | prepareOwner.accepted.rho.c1.a | session A | Every successful actual preparation has rho limb c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N030 | prepareOwner.accepted.rho.c1.b | session A | Every successful actual preparation has rho limb c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N031 | prepareOwner.accepted.semanticAlpha.c0.a | session A | Every successful actual preparation has semanticAlpha limb c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N032 | prepareOwner.accepted.semanticAlpha.c0.b | session A | Every successful actual preparation has semanticAlpha limb c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N033 | prepareOwner.accepted.semanticAlpha.c1.a | session A | Every successful actual preparation has semanticAlpha limb c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N034 | prepareOwner.accepted.semanticAlpha.c1.b | session A | Every successful actual preparation has semanticAlpha limb c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N035 | prepareOwner.accepted.coordinates.c0.a | session A | Every successful actual preparation has coordinates limb c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N036 | prepareOwner.accepted.coordinates.c0.b | session A | Every successful actual preparation has coordinates limb c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N037 | prepareOwner.accepted.coordinates.c1.a | session A | Every successful actual preparation has coordinates limb c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N038 | prepareOwner.accepted.coordinates.c1.b | session A | Every successful actual preparation has coordinates limb c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N039 | prepareOwner.accepted.claim.c0.c0.a | session A | Every successful actual preparation has claim limb c0.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N040 | prepareOwner.accepted.claim.c0.c0.b | session A | Every successful actual preparation has claim limb c0.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N041 | prepareOwner.accepted.claim.c0.c1.a | session A | Every successful actual preparation has claim limb c0.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N042 | prepareOwner.accepted.claim.c0.c1.b | session A | Every successful actual preparation has claim limb c0.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N043 | prepareOwner.accepted.claim.c1.c0.a | session A | Every successful actual preparation has claim limb c1.c0.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N044 | prepareOwner.accepted.claim.c1.c0.b | session A | Every successful actual preparation has claim limb c1.c0.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N045 | prepareOwner.accepted.claim.c1.c1.a | session A | Every successful actual preparation has claim limb c1.c1.a < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N046 | prepareOwner.accepted.claim.c1.c1.b | session A | Every successful actual preparation has claim limb c1.c1.b < 2147483647; all success guards and p/scratch witnesses stay shared. | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N047 | primitiveOwner.basis.s3_s4_mul | session A | Exact installed query basis primitive equation; universal helper instance. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N048 | primitiveOwner.basis.s3_s4_sub | session A | Exact installed query basis primitive equation; universal helper instance. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N049 | primitiveOwner.basis.s3_s4_double | session A | Exact installed query basis primitive equation; universal helper instance. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N050 | primitiveOwner.basis.zero | session A | Exact installed query basis primitive equation; universal helper instance. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N051 | primitiveOwner.basis.one | session A | Exact installed query basis primitive equation; universal helper instance. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N052 | primitiveOwner.arithmetic.s3_s4_s5_mulE.value | session A | Exact decoded arithmetic output under all original canonical/input/result guards. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N053 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.a | session A | Same output limb c0.c0.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N054 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.b | session A | Same output limb c0.c0.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N055 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.a | session A | Same output limb c0.c1.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N056 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.b | session A | Same output limb c0.c1.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N057 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.a | session A | Same output limb c1.c0.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N058 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.b | session A | Same output limb c1.c0.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N059 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.a | session A | Same output limb c1.c1.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N060 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.b | session A | Same output limb c1.c1.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N061 | primitiveOwner.arithmetic.s3_s4_s5_addE.value | session A | Exact decoded arithmetic output under all original canonical/input/result guards. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N062 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.a | session A | Same output limb c0.c0.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N063 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.b | session A | Same output limb c0.c0.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N064 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.a | session A | Same output limb c0.c1.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N065 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.b | session A | Same output limb c0.c1.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N066 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.a | session A | Same output limb c1.c0.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N067 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.b | session A | Same output limb c1.c0.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N068 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.a | session A | Same output limb c1.c1.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N069 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.b | session A | Same output limb c1.c1.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N070 | primitiveOwner.arithmetic.s3_s4_s9_mulK.value | session A | Exact decoded arithmetic output under all original canonical/input/result guards. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N071 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.a | session A | Same output limb c0.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N072 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.b | session A | Same output limb c0.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N073 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.a | session A | Same output limb c1.a < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N074 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.b | session A | Same output limb c1.b < 2147483647; not an independent output witness. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N075 | primitiveOwner.m31.multiply | session A | Decoded M31 primitive result agrees with the model on its actual successful return. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N076 | primitiveOwner.m31.double | session A | Decoded M31 primitive result agrees with the model on its actual successful return. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N077 | primitiveOwner.m31.one | session A | Decoded M31 primitive result agrees with the model on its actual successful return. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N078 | primitiveOwner.m31.subtract | session A | Decoded M31 primitive result agrees with the model on its actual successful return. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N079 | primitiveOwner.decoder.decode | session A | Every successful bounded four-wide opening decode agrees with the selected wire slice. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N080 | primitiveOwner.line | session A | Actual op16 line result equals lineWithInverses on the same values and inverse carrier. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N081 | primitiveOwner.line_canonical.c0.c0.a | session A | Same successful op16 output limb c0.c0.a < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N082 | primitiveOwner.line_canonical.c0.c0.b | session A | Same successful op16 output limb c0.c0.b < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N083 | primitiveOwner.line_canonical.c0.c1.a | session A | Same successful op16 output limb c0.c1.a < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N084 | primitiveOwner.line_canonical.c0.c1.b | session A | Same successful op16 output limb c0.c1.b < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N085 | primitiveOwner.line_canonical.c1.c0.a | session A | Same successful op16 output limb c1.c0.a < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N086 | primitiveOwner.line_canonical.c1.c0.b | session A | Same successful op16 output limb c1.c0.b < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N087 | primitiveOwner.line_canonical.c1.c1.a | session A | Same successful op16 output limb c1.c1.a < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N088 | primitiveOwner.line_canonical.c1.c1.b | session A | Same successful op16 output limb c1.c1.b < 2147483647. | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N089 | geoLeaves.point.x | session A | Geometry primitive successful output x is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N090 | geoLeaves.point.y | session A | Geometry primitive successful output y is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N091 | geoLeaves.line.value | session A | Geometry primitive successful output value is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N092 | geoLeaves.multiply.value | session A | Geometry primitive successful output value is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N093 | geoLeaves.double.value | session A | Geometry primitive successful output value is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N094 | geoLeaves.one.value | session A | Geometry primitive successful output value is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N095 | geoLeaves.subtract.value | session A | Geometry primitive successful output value is canonical, with every original guard. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N096 | domain.fibre.identity | session A | Actual geometry fibre output identity has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N097 | domain.fibre.bound | session A | Actual geometry fibre output bound has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N098 | domain.point.x | session A | Actual geometry point output x has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N099 | domain.point.y | session A | Actual geometry point output y has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N100 | domain.line.value | session A | Actual geometry line output value has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N101 | domain.multiply.value | session A | Actual geometry multiply output value has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N102 | domain.double.value | session A | Actual geometry double output value has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N103 | domain.one.value | session A | Actual geometry one output value has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N104 | domain.subtract.value | session A | Actual geometry subtract output value has the exact model-domain meaning; same result witness. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N105 | geometry.multiply | session A | Exact geometry helper equation in the conditional source/model composition. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N106 | geometry.one | session A | Exact geometry helper equation in the conditional source/model composition. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N107 | geometry.inverse | session A | Exact geometry helper equation in the conditional source/model composition. | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N108 | prepare_S1.queries | session A | Same TX1 preparation-to-model law queries; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N109 | prepare_S1.rho_eq | session A | Same TX1 preparation-to-model law rho_eq; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N110 | prepare_S1.rho_canonical.c0.a | session A | Same TX1 preparation-to-model law rho_canonical limb c0.a; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N111 | prepare_S1.rho_canonical.c0.b | session A | Same TX1 preparation-to-model law rho_canonical limb c0.b; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N112 | prepare_S1.rho_canonical.c1.a | session A | Same TX1 preparation-to-model law rho_canonical limb c1.a; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N113 | prepare_S1.rho_canonical.c1.b | session A | Same TX1 preparation-to-model law rho_canonical limb c1.b; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N114 | prepare_S1.alpha1 | session A | Same TX1 preparation-to-model law alpha1; shared data/rho/q and actual run.p. | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N115 | tx1_saved | lead | The ACTUAL saved Vec equals Tx2N_Reader.writer H stored publicBytes of prepared Context/data/rho/q and the model ten-state accumulator. | Derive the full Context, Prepared and physical writer encoding equation on this same TX1 run. Cons_Ten proves the accumulator under preparation/read laws but does not prove this complete Vec equation. |
| N116 | ten.parseReached | lead | The particular transcript used for the strengthened ten-state conclusion parses the same authParsed; distinct from mere existence in entry.parsed. | Associate the selected transcript with the same source proof and matching-data read; existential parser success alone does not identify an arbitrary transcript. |
| N117 | prefixBound | external | Universal query-budget bound for adversary before TX1. | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |
| N118 | choiceBound | external | Universal query-budget bound for chooseSecond on every input and saved Vec. | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |

### All remaining P rows and accountable blockers

This list includes actual antecedents and remaining deployment rows, explicitly
labelled; aliases are not independent gates. Ownership is accountable owner,
not a claim about a concurrent worker's completion.

| ID | Scope | Owner | Remaining law / deliverable | Waiting on |
|---|---|---|---|---|
| L083 | actual antecedent | lead | accepted1 | Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem. |
| L084 | actual antecedent | lead | accepted2 | Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem. |
| L085 | actual antecedent | lead | p.hL | Unchanged FS2.Params data-carrier law (unused parameter); not an implementation/security closure. |
| L086 | actual antecedent | lead | p.encLen | Unchanged FS2.Params data-carrier law (unused parameter); not an implementation/security closure. |
| L087 | actual antecedent | lead | p.decEnc | Unchanged FS2.Params data-carrier law (unused parameter); not an implementation/security closure. |
| L094 | actual antecedent | lead | history.savedAtCommit | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. |
| L095 | actual antecedent | lead | history.loadedAtEntry | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. |
| L096 | actual antecedent | lead | history.noInterveningWrite | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. |
| L097 | actual antecedent | lead | p2prime.binding.proof | Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient. |
| L098 | actual antecedent | lead | p2prime.binding.pub | Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient. |
| L099 | actual antecedent | lead | entry.parsed | Associate the actual accepted proof with its reached parsed transcript on this pair. |
| L110 | actual antecedent | session A | r0.field0 | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L111 | actual antecedent | session A | r0.field4 | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L112 | actual antecedent | session A | r0.add | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L113 | actual antecedent | session A | r0.quarter_run | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L114 | actual antecedent | session A | r0.multiply | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L115 | actual antecedent | session A | r0.evaluate | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L116 | actual antecedent | session A | r1.field0 | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L117 | actual antecedent | session A | r1.field4 | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L118 | actual antecedent | session A | r1.add | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L119 | actual antecedent | session A | r1.quarter_run | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L120 | actual antecedent | session A | r1.multiply | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L121 | actual antecedent | session A | r1.evaluate | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L122 | actual antecedent | lead | s2 | Derive the exact resumed Prepared variant and alpha/slice observations from the accepted source calls. |
| L123 | actual antecedent | lead | ha0 | Derive the exact resumed Prepared variant and alpha/slice observations from the accepted source calls. |
| L124 | actual antecedent | lead | ha1 | Derive the exact resumed Prepared variant and alpha/slice observations from the accepted source calls. |
| L125 | actual antecedent | session A | hw | Supply the same native newWeights/pair/dot primitive return and its model interpretation. |
| L126 | actual antecedent | lead | has | Derive the exact resumed Prepared variant and alpha/slice observations from the accepted source calls. |
| L127 | actual antecedent | session A | hp | Supply the same native newWeights/pair/dot primitive return and its model interpretation. |
| L128 | actual antecedent | session A | hd | Supply the same native newWeights/pair/dot primitive return and its model interpretation. |
| L129 | actual antecedent | lead | hi | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L130 | actual antecedent | lead | hq | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L131 | actual antecedent | lead | read | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L132 | actual antecedent | lead | decoded | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L133 | actual antecedent | session A | pairing_S3_S5_S9.round0.boundary | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L134 | actual antecedent | session A | pairing_S3_S5_S9.round0.quarter | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L135 | actual antecedent | session A | pairing_S3_S5_S9.round0.eval | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L136 | actual antecedent | session A | pairing_S3_S5_S9.round1.boundary | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L137 | actual antecedent | session A | pairing_S3_S5_S9.round1.quarter | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L138 | actual antecedent | session A | pairing_S3_S5_S9.round1.eval | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L139 | actual antecedent | session A | pairing_S3_S5_S9.claim | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L140 | actual antecedent | session A | pairing_S3_S5_S9.alpha0 | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L141 | actual antecedent | session A | pairing_S3_S5_S9.alpha1 | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L142 | actual antecedent | session A | pairing_S3_S5_S9.pair | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L143 | actual antecedent | session A | matches_S4_S7 | Prove actual S4/S7 matching relation for all selected queries. |
| L144 | actual antecedent | session A | semantic_S3_S9.EquationEndpoint.initial | Bind same source semantic/initial/chain/terminal equations from S3/S9. |
| L145 | actual antecedent | session A | semantic_S3_S9.EquationEndpoint.chain | Bind same source semantic/initial/chain/terminal equations from S3/S9. |
| L146 | actual antecedent | session A | semantic_S3_S9.EquationEndpoint.terminal | Bind same source semantic/initial/chain/terminal equations from S3/S9. |
| L147 | actual antecedent | session A | dot_S5 | Prove actual S5 dot product equals the selected opening/accumulator model. |
| L148 | actual antecedent | session A | canonical_S3_S4_S5_S9 | Prove same source round/pair/dot/rhs canonical observation roundtrips. |
| L151 | actual antecedent | lead | i.data.Functional.map_add | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. |
| L152 | actual antecedent | lead | i.data.Functional.map_smul | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. |
| L153 | actual antecedent | lead | tr.statement.initFits | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. |
| L154 | actual antecedent | external | hqueries | Prove total ByteProver query budget in the chosen oracle work model. |
| L157 | actual antecedent | lead | canonicalJoin.verifier | Raw canonical accepted source/frozen2 equality, including complete ordered oracle log; RawJ_ owner work is not imported. |
| L159 | actual antecedent | lead | StoredCarrierBinding | Identify complete accepted runtime RunView with this same source program and oracle world. |
| N001 | actual antecedent | session A | prepareOwner.accepted.variant | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N002 | actual antecedent | session A | prepareOwner.accepted.queries | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N003 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N004 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N005 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N006 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N007 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N008 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N009 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N010 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N011 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N012 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N013 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N014 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N015 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N016 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N017 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N018 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N019 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N020 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N021 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N022 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N023 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N024 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N025 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N026 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N027 | actual antecedent | session A | prepareOwner.accepted.rho.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N028 | actual antecedent | session A | prepareOwner.accepted.rho.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N029 | actual antecedent | session A | prepareOwner.accepted.rho.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N030 | actual antecedent | session A | prepareOwner.accepted.rho.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N031 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N032 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N033 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N034 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N035 | actual antecedent | session A | prepareOwner.accepted.coordinates.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N036 | actual antecedent | session A | prepareOwner.accepted.coordinates.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N037 | actual antecedent | session A | prepareOwner.accepted.coordinates.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N038 | actual antecedent | session A | prepareOwner.accepted.coordinates.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N039 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N040 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N041 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N042 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N043 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N044 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N045 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N046 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N047 | actual antecedent | session A | primitiveOwner.basis.s3_s4_mul | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N048 | actual antecedent | session A | primitiveOwner.basis.s3_s4_sub | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N049 | actual antecedent | session A | primitiveOwner.basis.s3_s4_double | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N050 | actual antecedent | session A | primitiveOwner.basis.zero | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N051 | actual antecedent | session A | primitiveOwner.basis.one | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N052 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.value | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N053 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N054 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N055 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N056 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N057 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N058 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N059 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N060 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N061 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.value | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N062 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N063 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N064 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N065 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N066 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N067 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N068 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N069 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N070 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.value | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N071 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N072 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N073 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N074 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N075 | actual antecedent | session A | primitiveOwner.m31.multiply | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N076 | actual antecedent | session A | primitiveOwner.m31.double | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N077 | actual antecedent | session A | primitiveOwner.m31.one | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N078 | actual antecedent | session A | primitiveOwner.m31.subtract | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N079 | actual antecedent | session A | primitiveOwner.decoder.decode | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N080 | actual antecedent | session A | primitiveOwner.line | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N081 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N082 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N083 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N084 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N085 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N086 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N087 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N088 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N089 | actual antecedent | session A | geoLeaves.point.x | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N090 | actual antecedent | session A | geoLeaves.point.y | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N091 | actual antecedent | session A | geoLeaves.line.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N092 | actual antecedent | session A | geoLeaves.multiply.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N093 | actual antecedent | session A | geoLeaves.double.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N094 | actual antecedent | session A | geoLeaves.one.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N095 | actual antecedent | session A | geoLeaves.subtract.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N096 | actual antecedent | session A | domain.fibre.identity | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N097 | actual antecedent | session A | domain.fibre.bound | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N098 | actual antecedent | session A | domain.point.x | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N099 | actual antecedent | session A | domain.point.y | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N100 | actual antecedent | session A | domain.line.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N101 | actual antecedent | session A | domain.multiply.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N102 | actual antecedent | session A | domain.double.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N103 | actual antecedent | session A | domain.one.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N104 | actual antecedent | session A | domain.subtract.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N105 | actual antecedent | session A | geometry.multiply | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N106 | actual antecedent | session A | geometry.one | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N107 | actual antecedent | session A | geometry.inverse | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N108 | actual antecedent | session A | prepare_S1.queries | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N109 | actual antecedent | session A | prepare_S1.rho_eq | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N110 | actual antecedent | session A | prepare_S1.rho_canonical.c0.a | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N111 | actual antecedent | session A | prepare_S1.rho_canonical.c0.b | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N112 | actual antecedent | session A | prepare_S1.rho_canonical.c1.a | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N113 | actual antecedent | session A | prepare_S1.rho_canonical.c1.b | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N114 | actual antecedent | session A | prepare_S1.alpha1 | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N115 | actual antecedent | lead | tx1_saved | Derive the full Context, Prepared and physical writer encoding equation on this same TX1 run. Cons_Ten proves the accumulator under preparation/read laws but does not prove this complete Vec equation. |
| N116 | actual antecedent | lead | ten.parseReached | Associate the selected transcript with the same source proof and matching-data read; existential parser success alone does not identify an arbitrary transcript. |
| N117 | actual antecedent | external | prefixBound | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |
| N118 | actual antecedent | external | choiceBound | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |
| L165 | deployment only | lead | shape full semantic/transcript join | Header/shape value installed; full source semantic/transcript association remains in L129-L132 and raw join. |
| L166 | deployment only | lead | batch source Result/effects | Installed source batch effects are identified by driver construction; native lowering/adoption/effect association still required. |
| L168 | deployment alias | lead | prepare Context/Data binding | Same Context/data/preparation and saved-byte association remains as N preparation laws and tx1_saved; not discharged by state arithmetic. |
| L176 | deployment only | session A | S6 native decoded/public transport | Semantic source getters/cuts compose, but native ownership/error/cleanup/adoption remains outside the kernel statement. |
| L177 | deployment only | lead | Claims native std slots | Arbitrary Claims reserve/intoBox data dictionary has no full native ownership/abort/effects interpretation. |
| L178 | deployment alias | session A | remaining primitive instances | Covered explicitly by N001-N114 primitive/preparation law leaves; do not add another count for this umbrella. |
| L179 | deployment only | lead | library/native frame | SDK borrow trust retained; concrete allocator/library/native frame and source association remain deployment obligations. |
| L180 | deployment alias | lead | history protection / Pool-ASQ8 | Specific cross-transaction history protection remains L094-L096; runtime rollback semantics alone is insufficient. |
| L181 | deployment only | lead | oracle model order | Complete source Program equality is proved; ordered source-to-frozen2 model event/projection association remains raw L157/GExq work. |
| L182 | deployment alias | lead | raw canonical join | Same obligation as literal L157 at this installed source, not a second independent gate. |
| L185 | deployment alias | lead | deployed stored experiment | Same obligation as literal L159 at this installed source, not a second independent gate. |
| L186 | deployment only | lead | source lowering to frozen ELFs | Source-to-SBF/artifact association for the exact frozen ELFs remains; no new binary proof. |
| L187 | deployment only | lead | coherent frozen replay | Only coherent cached focused composition audited; full frozen dependency release replay not run. |
| L188 | deployment only | lead | final axioms/trust audit | Current top standard-axiom audit passes; final release dependency/trust/adoption audit remains. |
| L195 | deployment only | lead | P6Boundary.oracle | Actual native total-oracle/source association remains, distinct from success-only RuntimeSyscall; no P6-boundary binder in this top. |
| L196 | deployment only | lead | P6Boundary.binary_parent | Actual native binary-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L197 | deployment only | lead | P6Boundary.occupied_parent | Actual native occupied-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L198 | deployment only | lead | P6Boundary.sibling_parent | Actual native sibling-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L199 | deployment only | lead | P6Boundary.leaf | Actual native leaf callback/source association remains a deployment obligation; no leaf gate binder here. |

### Requested removal claims: statement-level reconciliation

| Reported row / claim | Recount finding / discrepancy |
|---|---|
| L089 | Absent: old unguarded FirstMarks removed. No discrepancy on this top; it does not prove the old unguarded law. |
| L090 | Absent: old unguarded SecondMarks removed. No discrepancy on this top. |
| writer admission | Admitted is an OUTPUT, not a premise. Qualified: immutable prepareOwner's 46 atomic laws plus primitiveOwner remain; not unconditional native writer certification. |
| L164 | Removed: one checked dictionary and same f,s/run, no compatibility premise. |
| L091 | Removed: writer header derived. |
| L092 | Removed: writer size derived. |
| L093 | Removed: reader checkedHeader derived. |
| L100 | Removed: batch0 physical start derived. |
| L101 | Removed: batch0 physical finish derived. |
| L102 | Removed: batch0 physical bound derived. |
| L103 | Removed: batch0 physical index derived. |
| L104 | Removed: batch1 physical start derived. |
| L105 | Removed: batch1 physical finish derived. |
| L106 | Removed: batch1 physical bound derived. |
| L107 | Removed: batch1 physical index derived. |
| L108 | Removed: y1 length derived. |
| L109 | Removed: y1 index derived. |
| authenticated_S1 | Absent in the sole finish and strengthened ten branch. Removal confirmed with the documented collision alternative; seven prepare_S1 laws remain. |
| L158 | Removed: canonical annotation derived; raw L157 remains. |
| L183 | Removed: two passes derived; raw L157 and runtime L159 remain. |
| L184 | Removed: corrected conditional PerAttempt endpoint is an actual conclusion, including the zero-query bound. It is not an unconditional deployed guarantee. |
| L175 | Successful finish effects are an output. Removal confirmed on the shared tuple; source/runtime/artifact association and round/pair/dot laws remain as documented. |
| L172 | Native/helper reader and exact OnRun effects are outputs. Removal confirmed on the shared tuple; extraction/native source association remains as documented, and saved_ten depends on tx1_saved. |
| L160 | Removed at this constructed instance: Program equality and dictionary identities proved. No claim that every arbitrary Implementation is installed. |
| L149 saved_ten | Removed as an input. Material replacement boundary: tx1_saved remains a whole saved-Vec/model encoding equation. |
| L150 twelve | Removed as an input. Primitive/domain/read/preparation and saved-Vec boundaries still needed. |

Direct comparison with `DrvC_HANDOFF.md`, `auth-s1-20261026/HANDOFF.md` and
`T2Nat_HANDOFF.md` finds no disagreement with their SCOPED named-removal claims.
The material qualifications above are retained documented boundaries, not
contradictions of those reports. The initial Stage1 independent TX2 packaging
is superseded by the shared tuple in Stage2. Newly inventoried P rows largely
expose inherited CPhy/owner contracts; they are not all introduced by Cons_.

No contradiction/vacuity-suspect C antecedent from the old endpoints survives.
This is not a joint inhabitation proof for all remaining runtime/model premises.
No imported candidate from RawJ_, NP6_ or Low2_ is credited or changed.
Source-to-ELF association and the full release target remain open.

### Validation and handoff

Thirty-nine Lean compile attempts of60, zero Kani of0; zero dependency builds.
Fifteen failed development versions are retained and excluded: 001,012,013,015,
018,019,020,021,023,026,028,030,032,034,035. Compiler-generated sorryAx in failed
versions is never accepted. Eleven default-heartbeat failures were isolated and
split; no wall timeout/memory kill/cap/heartbeat increase occurred. The decisive
source-shape correction is in Cons_036: the concrete native TX2 base must include
Op5T's installed batch, rather than reducing unequal arbitrary dictionaries.
Cons_037/038 pass the final Pair/Top; Cons_039 prints all five new theorem audits,
all exactly [propext, Classical.choice, Quot.sound]. Current native/finish/base/
caller/result definitions also passed independently. Every actual call uses the
unchanged S2W launchers, lake env lean -j1 -M7000 -DElab.async=false, separate
scopes MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. One own scope at a time;
initial inventory observed one NP6 scope. No unchanged timed-out source+dependency
rerun, package replay or launcher/infrastructure edit occurred.

Per-attempt source revisions, exact source/dependency hashes, targets, exits,
wall/RSS/swap and full axiom/error lines are in the receipts and source snapshots.
Cons_validation.json validates current sources against the accepted receipts,
field coverage, deduplication/totals and append-only preservation of prior ledger
text. Unchanged cached canonical/SInt2/DrvC/T2Nat/AuS1/Tx2N dependencies were
reused; this is a focused coherent composition, not a frozen release rebuild.

No shipped or cfg(kani) file changed, so the three-ELF rebuild trigger did not
fire. Pins inherited, not freshly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No session A live worktree/candidate, foreign module, key or release scope was
changed. Commits are local; no push. Next concrete deliverables are raw L157,
complete runtime L159, same saved-Vec/Context equation and actual source/model
primitive instances, followed by global event and source/artifact association.

## Recount on Rc2_Top (2026-10-26)

**Actual theorem `AspisR1.Rc2_Top.deployed`; S2 OPEN, target not yet established.**
Branch `codex/cx-recount2-20261026`. Evidence and reproducible audit:
`evidence/recount2-20261026/Rc2_premises.json`, `Rc2_recount.py`,
`Rc2_022/stdout.log`, `Rc2_validation.json` and `Rc2_HANDOFF.md`.

This applies Ledger_003–005 and Cons's counting method to the complete actual
top and its factored conclusions: atomic conjunctive leaves, quantified law
families, SAME existential witnesses/guards, shared-dictionary deduplication.
The fresh successful kernel transcript prints both Cons and Rc2 statements,
Rc2_Result/Base/Events/Protection, NP6 contents and selected std dictionary,
T2R finish/ten/caller/continuation/acceptance, and retained SDK/std/allocator/
entry/extraction/owner structures. Rc2_field_catalog mechanically extracts the
printed structures. Preparation/query/geometry nested fields are freshly printed too; the unchanged
Cons_008/010 and Ledger_003–005 inventories are retained as the before evidence,
with source hashes checked against the same repository baseline; no passing import is credited as a proof of those
fields. The renderer makes explicit reviewed correspondence/classification
judgments, then mechanically enumerates rows/diffs/totals; it is not a logical
discharge checker. The baseline is Cons_premises.json's 281 retained rows, not
its already-removed historical rows. All 281 plus five new guards are accounted.

Selected composition: T2R's unchanged frozen parameters and source-selected
TX2 reader, NP6 initial/pending and parsed Claims content, exact PoolT accepted
copy plus metadata/other-cell frame, CPS source-bank events, CPP atomic ordered
oracle-log preservation, CPR rollback and guarded bank protection. Every
accepted cut/run/Claims/TX2 witness remains shared. The source-bank recorder is
parameterized by arbitrary initial/actions, and its saved value is the SAME
accepted TX1 return. No physical validator trace is inferred from that equality.

`Rc2_Install.select` explicitly replaces only the free Claims std slot by
NP6_StdModel.calls reservation, preserving the other fields; `configuration`
also retains T2R's existing first-constant installation. `standard` and
`dictionary` prove compatibility rather than asking for it. This is a selected
instance, not a claim that arbitrary free std dictionaries equal NP6. NP6's
full source-helper certificate supplies the scoped shipped unsafe/reference
interpretation; Lean slot specialization alone would give no native credit.
Allocator/ABI/SDK/extraction/hash/runtime and source-to-ELF boundaries remain.

**No frozen3 candidate or runtime persistence law is selected.** Interrupted
attempt015 had an extra guarded Rc2_History corollary; attempts018–020 remove
it from the selected result/top. The standalone development module is retained
as excluded work. CPS's unconditional source-event part remains; L094–L096 and
the L180 alias remain. No premise is erased merely by moving it into a record.
The new bank-model conclusions retain five explicit proof guards, counted below.
They do not gate inherited headline/finish outputs. No new T item is adopted.

### Totals per class and owner

“Actual antecedent” includes application guards inside advertised conditional
conclusions, as in Cons; it does not mean every such row is an outer root binder.
New bank guards are scoped separately in their row role. “Deployment alias” is
an umbrella, excluded from the deduplicated total. Counts are syntactic audit
families and do not measure a security percentage or independent proof gates.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
| actual antecedent | 82 | 171 | 0 | 23 | 145 | 85 |
| deployment only | 6 | 13 | 0 | 12 | 1 | 6 |
| deployment alias | 0 | 5 | 0 | 4 | 1 | 0 |
| all retained audit rows | 88 | 189 | 0 | 39 | 147 | 91 |
| deduplicated actual plus non-alias deployment | 88 | 184 | 0 | 35 | 146 | 91 |

| Scope / owner | T | P | C |
|---|---:|---:|---:|
| actual antecedent / lead | 0 | 23 | 0 |
| actual antecedent / session A | 0 | 145 | 0 |
| actual antecedent / external | 82 | 3 | 0 |
| deployment only / lead | 0 | 12 | 0 |
| deployment only / session A | 0 | 1 | 0 |
| deployment only / external | 6 | 0 | 0 |
| deployment alias / lead | 0 | 4 | 0 |
| deployment alias / session A | 0 | 1 | 0 |
| deployment alias / external | 0 | 0 | 0 |
| all retained audit rows / lead | 0 | 39 | 0 |
| all retained audit rows / session A | 0 | 147 | 0 |
| all retained audit rows / external | 88 | 3 | 0 |
| deduplicated actual plus non-alias deployment / lead | 0 | 35 | 0 |
| deduplicated actual plus non-alias deployment / session A | 0 | 146 | 0 |
| deduplicated actual plus non-alias deployment / external | 88 | 3 | 0 |

Cons actual: 82T+174P. Eight Cons actual P families are removed by the checked
T2R composition; five CPR guard families are newly exposed, giving **82T+171P**.
If inspecting only inherited security conclusions, the five additional guards
do not apply: that slice is 82T+166P. L177 removes one deployment P family at
the selected Claims instance. No T/C change. L174 was ALREADY absent in Cons;
NP6 strengthens its same-run output, so there is no second subtraction. L179
is PARTIAL: Claims-local frame/ownership/cleanup is certified, whole-library/
native/runtime/artifact association is retained under that broader row.
L151–L153 remain structural model-carrier laws under the original universal
continuations; scoped instances are not a global source-arithmetic discharge.

### Pending OWNER routes and lead rows that can proceed

(a) Frozen3 adoption is an unadopted candidate replacement route for L157/L159;
L181/L182/L185 are the corresponding source/order/transport inventory and
aliases. Adoption alone is not claimed to close them. (b) Runtime law adoption
AND authoritative physical contract-game clarification gate L094–L096/L180;
ordinary-key eligibility, physical account identity, source action order and
final parent success cannot be hidden as experiment data. (c) Session A's
own rows remain pending; the additional lead-owned binding/source/model rows
explicitly tagged c consume their S1/S6 or S3/S4 interpretations. No live
session A worktree/candidate was touched. Tags describe the adopted work routes;
a different proof could replace a route without an OWNER decision.

Lead P rows with NONE of a/b/c: **21 deduplicated** (11 actual, 10 non-alias deployment). All audit rows including aliases: 21. IDs: L083, L084, L099, L151, L152, L153, L166, L179, L186, L187, L188, L195, L196, L197, L198, L199, Rc2_P001, Rc2_P002, Rc2_P003, Rc2_P004, Rc2_P005.

This includes the two success-event restrictions and three structural carrier
rows: “can proceed” is not a claim that those are unproved independent gates.
Global artifact/replay/trust work is untagged because its own action can proceed
independently; final release use still depends on all unresolved source cones.

### Complete row diff against Cons_Top recount

| ID | Name | Class / owner | Status / scope | Exact correspondence or blocker |
|---|---|---|---|---|
| L001 | sdk.account_data_cell.data-cell identity | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L002 | sdk.account_data_cell.lamports-cell identity | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L003 | sdk.account_data_cell.shared data-cell alias agreement | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L004 | sdk.account_data_cell.live data/lamports separation | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L005 | sdk.cell_payload.typed cell payload equality | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L006 | sdk.cell_counter.counter equality | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L007 | sdk.cell_counter.live-guard lookup equality | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L008 | sdk.guard_liveness.live guard identity | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L009 | sdk.guard_liveness.allocation liveness | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L010 | sdk.guard_liveness.descriptor identity | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L011 | sdk.shared_ok.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L012 | sdk.shared_ok.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L013 | sdk.shared_err.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L014 | sdk.shared_err.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L015 | sdk.exclusive_ok.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L016 | sdk.exclusive_ok.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L017 | sdk.exclusive_err.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L018 | sdk.exclusive_err.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L019 | sdk.shared_deref.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L020 | sdk.shared_deref.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L021 | sdk.exclusive_deref.read.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L022 | sdk.exclusive_deref.read.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L023 | sdk.exclusive_deref.write.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L024 | sdk.exclusive_deref.write.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L025 | sdk.guard_move.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L026 | sdk.guard_move.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L027 | sdk.shared_drop.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L028 | sdk.shared_drop.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L029 | sdk.exclusive_drop.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L030 | sdk.exclusive_drop.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L031 | sdk.error_move_drop.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L032 | sdk.error_move_drop.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L033 | sdk.borrow_frame.Matches.reply | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L034 | sdk.borrow_frame.Matches.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L035 | std.slice_copy_from_slice | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L036 | admission1.entry.valid.uniqueToken | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L037 | admission1.entry.valid.uniqueOwner | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L038 | admission1.entry.valid.counterLower | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L039 | admission1.entry.valid.counterUpper | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L040 | admission1.entry.valid.counterEquation | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L041 | admission1.entry.valid.exclusive.externalZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L042 | admission1.entry.valid.exclusive.sharedZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L043 | admission1.entry.valid.exclusive.one | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L044 | admission1.entry.valid.externalNegative.sharedZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L045 | admission1.entry.valid.externalNegative.exclusiveZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L046 | admission1.entry.valid.guardAllocated | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L047 | admission1.entry.valid.guardDescriptor | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L048 | admission1.entry.valid.liveSeparate | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L049 | admission1.entry.valid.liveAllocated | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L050 | admission1.entry.freshGuards | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L051 | admission1.entry.noExternalBorrows | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L052 | admission1.entry.liveAccount | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L053 | admission1.entry.counterZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L054 | admission1.entry.sharedCellsOnlyEqualKeys | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L055 | admission1.entry.duplicateKeysShareCell | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L056 | admission1.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L057 | admission2.entry.valid.uniqueToken | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L058 | admission2.entry.valid.uniqueOwner | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L059 | admission2.entry.valid.counterLower | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L060 | admission2.entry.valid.counterUpper | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L061 | admission2.entry.valid.counterEquation | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L062 | admission2.entry.valid.exclusive.externalZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L063 | admission2.entry.valid.exclusive.sharedZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L064 | admission2.entry.valid.exclusive.one | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L065 | admission2.entry.valid.externalNegative.sharedZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L066 | admission2.entry.valid.externalNegative.exclusiveZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L067 | admission2.entry.valid.guardAllocated | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L068 | admission2.entry.valid.guardDescriptor | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L069 | admission2.entry.valid.liveSeparate | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L070 | admission2.entry.valid.liveAllocated | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L071 | admission2.entry.freshGuards | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L072 | admission2.entry.noExternalBorrows | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L073 | admission2.entry.liveAccount | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L074 | admission2.entry.counterZero | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L075 | admission2.entry.sharedCellsOnlyEqualKeys | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L076 | admission2.entry.duplicateKeysShareCell | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L077 | admission2.related | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L078 | extraction.stage1 | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L079 | extraction.stage2 | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L080 | extraction.digestSource | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L081 | p1 | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L082 | syscall | T / external | still present / actual antecedent | Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance. |
| L083 | accepted1 | P / lead | still present / actual antecedent | Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem. |
| L084 | accepted2 | P / lead | still present / actual antecedent | Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem. |
| L085 | p.hL | P / lead | removed / actual antecedent | Exact original frozen parameter instance; no free Params binder |
| L086 | p.encLen | P / lead | removed / actual antecedent | Exact bounded original encoder instance |
| L087 | p.decEnc | P / lead | removed / actual antecedent | Exact original decoder/encoder inverse |
| L094 | history.savedAtCommit | P / lead | still present / actual antecedent | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. |
| L095 | history.loadedAtEntry | P / lead | still present / actual antecedent | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. |
| L096 | history.noInterveningWrite | P / lead | still present / actual antecedent | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. |
| L097 | p2prime.binding.proof | P / lead | still present / actual antecedent | Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient. |
| L098 | p2prime.binding.pub | P / lead | still present / actual antecedent | Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient. |
| L099 | entry.parsed | P / lead | still present / actual antecedent | Associate the actual accepted proof with its reached parsed transcript on this pair. |
| L110 | r0.field0 | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L111 | r0.field4 | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L112 | r0.add | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L113 | r0.quarter_run | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L114 | r0.multiply | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L115 | r0.evaluate | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L116 | r1.field0 | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L117 | r1.field4 | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L118 | r1.add | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L119 | r1.quarter_run | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L120 | r1.multiply | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L121 | r1.evaluate | P / session A | still present / actual antecedent | Supply the two actual round return/evaluation laws from S3/S5/S9. |
| L122 | s2 | P / lead | removed / actual antecedent | SAME accepted installed op18 returns S2 |
| L123 | ha0 | P / lead | removed / actual antecedent | SAME op18 alpha0 physical read, returned as output |
| L124 | ha1 | P / lead | removed / actual antecedent | SAME op18 alpha1 physical read, returned as output |
| L125 | hw | P / session A | still present / actual antecedent | Supply the same native newWeights/pair/dot primitive return and its model interpretation. |
| L126 | has | P / lead | removed / actual antecedent | SAME op18 two-element alpha slice, returned as output |
| L127 | hp | P / session A | still present / actual antecedent | Supply the same native newWeights/pair/dot primitive return and its model interpretation. |
| L128 | hd | P / session A | still present / actual antecedent | Supply the same native newWeights/pair/dot primitive return and its model interpretation. |
| L129 | hi | P / lead | still present / actual antecedent | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L130 | hq | P / lead | still present / actual antecedent | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L131 | read | P / lead | still present / actual antecedent | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L132 | decoded | P / lead | still present / actual antecedent | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. |
| L133 | pairing_S3_S5_S9.round0.boundary | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L134 | pairing_S3_S5_S9.round0.quarter | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L135 | pairing_S3_S5_S9.round0.eval | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L136 | pairing_S3_S5_S9.round1.boundary | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L137 | pairing_S3_S5_S9.round1.quarter | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L138 | pairing_S3_S5_S9.round1.eval | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L139 | pairing_S3_S5_S9.claim | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L140 | pairing_S3_S5_S9.alpha0 | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L141 | pairing_S3_S5_S9.alpha1 | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L142 | pairing_S3_S5_S9.pair | P / session A | still present / actual antecedent | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. |
| L143 | matches_S4_S7 | P / session A | still present / actual antecedent | Prove actual S4/S7 matching relation for all selected queries. |
| L144 | semantic_S3_S9.EquationEndpoint.initial | P / session A | still present / actual antecedent | Bind same source semantic/initial/chain/terminal equations from S3/S9. |
| L145 | semantic_S3_S9.EquationEndpoint.chain | P / session A | still present / actual antecedent | Bind same source semantic/initial/chain/terminal equations from S3/S9. |
| L146 | semantic_S3_S9.EquationEndpoint.terminal | P / session A | still present / actual antecedent | Bind same source semantic/initial/chain/terminal equations from S3/S9. |
| L147 | dot_S5 | P / session A | still present / actual antecedent | Prove actual S5 dot product equals the selected opening/accumulator model. |
| L148 | canonical_S3_S4_S5_S9 | P / session A | still present / actual antecedent | Prove same source round/pair/dot/rhs canonical observation roundtrips. |
| L151 | i.data.Functional.map_add | P / lead | still present / actual antecedent | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. |
| L152 | i.data.Functional.map_smul | P / lead | still present / actual antecedent | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. |
| L153 | tr.statement.initFits | P / lead | still present / actual antecedent | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. |
| L154 | hqueries | P / external | still present / actual antecedent | Prove total ByteProver query budget in the chosen oracle work model. |
| L157 | canonicalJoin.verifier | P / lead | still present / actual antecedent | Raw canonical accepted source/frozen2 equality, including complete ordered oracle log; RawJ_ owner work is not imported. |
| L159 | StoredCarrierBinding | P / lead | still present / actual antecedent | Identify complete accepted runtime RunView with this same source program and oracle world. |
| N001 | prepareOwner.accepted.variant | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N002 | prepareOwner.accepted.queries | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N003 | prepareOwner.accepted.gamma.c0.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N004 | prepareOwner.accepted.gamma.c0.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N005 | prepareOwner.accepted.gamma.c0.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N006 | prepareOwner.accepted.gamma.c0.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N007 | prepareOwner.accepted.gamma.c1.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N008 | prepareOwner.accepted.gamma.c1.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N009 | prepareOwner.accepted.gamma.c1.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N010 | prepareOwner.accepted.gamma.c1.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N011 | prepareOwner.accepted.kappa.c0.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N012 | prepareOwner.accepted.kappa.c0.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N013 | prepareOwner.accepted.kappa.c0.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N014 | prepareOwner.accepted.kappa.c0.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N015 | prepareOwner.accepted.kappa.c1.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N016 | prepareOwner.accepted.kappa.c1.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N017 | prepareOwner.accepted.kappa.c1.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N018 | prepareOwner.accepted.kappa.c1.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N019 | prepareOwner.accepted.alpha.c0.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N020 | prepareOwner.accepted.alpha.c0.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N021 | prepareOwner.accepted.alpha.c0.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N022 | prepareOwner.accepted.alpha.c0.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N023 | prepareOwner.accepted.alpha.c1.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N024 | prepareOwner.accepted.alpha.c1.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N025 | prepareOwner.accepted.alpha.c1.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N026 | prepareOwner.accepted.alpha.c1.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N027 | prepareOwner.accepted.rho.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N028 | prepareOwner.accepted.rho.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N029 | prepareOwner.accepted.rho.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N030 | prepareOwner.accepted.rho.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N031 | prepareOwner.accepted.semanticAlpha.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N032 | prepareOwner.accepted.semanticAlpha.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N033 | prepareOwner.accepted.semanticAlpha.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N034 | prepareOwner.accepted.semanticAlpha.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N035 | prepareOwner.accepted.coordinates.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N036 | prepareOwner.accepted.coordinates.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N037 | prepareOwner.accepted.coordinates.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N038 | prepareOwner.accepted.coordinates.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N039 | prepareOwner.accepted.claim.c0.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N040 | prepareOwner.accepted.claim.c0.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N041 | prepareOwner.accepted.claim.c0.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N042 | prepareOwner.accepted.claim.c0.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N043 | prepareOwner.accepted.claim.c1.c0.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N044 | prepareOwner.accepted.claim.c1.c0.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N045 | prepareOwner.accepted.claim.c1.c1.a | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N046 | prepareOwner.accepted.claim.c1.c1.b | P / session A | still present / actual antecedent | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. |
| N047 | primitiveOwner.basis.s3_s4_mul | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N048 | primitiveOwner.basis.s3_s4_sub | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N049 | primitiveOwner.basis.s3_s4_double | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N050 | primitiveOwner.basis.zero | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N051 | primitiveOwner.basis.one | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N052 | primitiveOwner.arithmetic.s3_s4_s5_mulE.value | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N053 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N054 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N055 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N056 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N057 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N058 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N059 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N060 | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N061 | primitiveOwner.arithmetic.s3_s4_s5_addE.value | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N062 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N063 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N064 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N065 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N066 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N067 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N068 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N069 | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N070 | primitiveOwner.arithmetic.s3_s4_s9_mulK.value | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N071 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N072 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N073 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N074 | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N075 | primitiveOwner.m31.multiply | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N076 | primitiveOwner.m31.double | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N077 | primitiveOwner.m31.one | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N078 | primitiveOwner.m31.subtract | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N079 | primitiveOwner.decoder.decode | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N080 | primitiveOwner.line | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N081 | primitiveOwner.line_canonical.c0.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N082 | primitiveOwner.line_canonical.c0.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N083 | primitiveOwner.line_canonical.c0.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N084 | primitiveOwner.line_canonical.c0.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N085 | primitiveOwner.line_canonical.c1.c0.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N086 | primitiveOwner.line_canonical.c1.c0.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N087 | primitiveOwner.line_canonical.c1.c1.a | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N088 | primitiveOwner.line_canonical.c1.c1.b | P / session A | still present / actual antecedent | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. |
| N089 | geoLeaves.point.x | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N090 | geoLeaves.point.y | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N091 | geoLeaves.line.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N092 | geoLeaves.multiply.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N093 | geoLeaves.double.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N094 | geoLeaves.one.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N095 | geoLeaves.subtract.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N096 | domain.fibre.identity | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N097 | domain.fibre.bound | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N098 | domain.point.x | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N099 | domain.point.y | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N100 | domain.line.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N101 | domain.multiply.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N102 | domain.double.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N103 | domain.one.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N104 | domain.subtract.value | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N105 | geometry.multiply | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N106 | geometry.one | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N107 | geometry.inverse | P / session A | still present / actual antecedent | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. |
| N108 | prepare_S1.queries | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N109 | prepare_S1.rho_eq | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N110 | prepare_S1.rho_canonical.c0.a | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N111 | prepare_S1.rho_canonical.c0.b | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N112 | prepare_S1.rho_canonical.c1.a | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N113 | prepare_S1.rho_canonical.c1.b | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N114 | prepare_S1.alpha1 | P / session A | still present / actual antecedent | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. |
| N115 | tx1_saved | P / lead | still present / actual antecedent | Derive the full Context, Prepared and physical writer encoding equation on this same TX1 run. Cons_Ten proves the accumulator under preparation/read laws but does not prove this complete Vec equation. |
| N116 | ten.parseReached | P / lead | removed / actual antecedent | Source-selected parser already identifies proof bytes; direct Tx1Q_Model.ten retains every tr |
| N117 | prefixBound | P / external | still present / actual antecedent | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |
| N118 | choiceBound | P / external | still present / actual antecedent | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |
| L165 | shape full semantic/transcript join | P / lead | still present / deployment only | Header/shape value installed; full source semantic/transcript association remains in L129-L132 and raw join. |
| L166 | batch source Result/effects | P / lead | still present / deployment only | Installed source batch effects are identified by driver construction; native lowering/adoption/effect association still required. |
| L168 | prepare Context/Data binding | P / lead | still present / deployment alias | Same Context/data/preparation and saved-byte association remains as N preparation laws and tx1_saved; not discharged by state arithmetic. |
| L176 | S6 native decoded/public transport | P / session A | still present / deployment only | Semantic source getters/cuts compose, but native ownership/error/cleanup/adoption remains outside the kernel statement. |
| L177 | Claims native std slots | P / lead | removed / deployment only | Selected safe reserve/intoBox interpretation and full scoped shipped Claims helper certificate; arbitrary free std slot replaced explicitly. Existing allocator/runtime/extraction/artifact boundaries retained. |
| L178 | remaining primitive instances | P / session A | still present / deployment alias | Covered explicitly by N001-N114 primitive/preparation law leaves; do not add another count for this umbrella. |
| L179 | library/native frame | P / lead | still present / deployment only | NP6 closes Claims-local allocation/ownership/cleanup/frame only. Concrete whole library/native frame, allocator interpretation and source-to-artifact association remain outside that helper scope. |
| L180 | history protection / Pool-ASQ8 | P / lead | still present / deployment alias | L094-L096 remain: owner must clarify the physical two-transaction security game and adopt or replace TwoTransactionLaw; prove ordinary-key eligibility, physical identity, final parent success and source-ordered action association. |
| L181 | oracle model order | P / lead | still present / deployment only | Complete source Program equality is proved; ordered source-to-frozen2 model event/projection association remains raw L157/GExq work. |
| L182 | raw canonical join | P / lead | still present / deployment alias | Same obligation as literal L157 at this installed source, not a second independent gate. |
| L185 | deployed stored experiment | P / lead | still present / deployment alias | Same obligation as literal L159 at this installed source, not a second independent gate. |
| L186 | source lowering to frozen ELFs | P / lead | still present / deployment only | Source-to-SBF/artifact association for the exact frozen ELFs remains; no new binary proof. |
| L187 | coherent frozen replay | P / lead | still present / deployment only | Only coherent cached focused composition audited; full frozen dependency release replay not run. |
| L188 | final axioms/trust audit | P / lead | still present / deployment only | Current top standard-axiom audit passes; final release dependency/trust/adoption audit remains. |
| L189 | P7 compiler/LLVM/toolchain | T / external | still present / deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L190 | P6 Kani association | T / external | still present / deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L191 | runtime allocator/entrypoint/syscall | T / external | still present / deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L192 | TrustedStd.option_ok_or | T / external | still present / deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L193 | TrustedStd.result_unwrap32 | T / external | still present / deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L194 | cryptographic security contract | T / external | still present / deployment only | Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder. |
| L195 | P6Boundary.oracle | P / lead | still present / deployment only | Actual native total-oracle/source association remains, distinct from success-only RuntimeSyscall; no P6-boundary binder in this top. |
| L196 | P6Boundary.binary_parent | P / lead | still present / deployment only | Actual native binary-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L197 | P6Boundary.occupied_parent | P / lead | still present / deployment only | Actual native occupied-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L198 | P6Boundary.sibling_parent | P / lead | still present / deployment only | Actual native sibling-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L199 | P6Boundary.leaf | P / lead | still present / deployment only | Actual native leaf callback/source association remains a deployment obligation; no leaf gate binder here. |
| Rc2_P001 | protection.keyLaw | P / lead | newly present / actual antecedent | Prove the installed op36 key-equality/source interpretation; adapter remains data-only and arbitrary. Needed for new bank effect/protection conclusions. |
| Rc2_P002 | protection.owner | P / lead | newly present / actual antecedent | Associate an arbitrary protected-bank key with the verifier program owner. The accepted writer derives this in its scoped bank model; the top does not identify every arbitrary before/key with that writer. |
| Rc2_P003 | protection.marker.nonempty | P / lead | newly present / actual antecedent | Prove nonempty data at the arbitrary protected-bank key; first conjunct of Initialized. Accepted writer shape does not identify the universal before/key. |
| Rc2_P004 | protection.marker.tag | P / lead | newly present / actual antecedent | Prove the exact initialized tag at that arbitrary protected-bank key; second conjunct of Initialized. Accepted writer derives its local marker, but this bank/key association remains. |
| Rc2_P005 | protection.positive | P / lead | newly present / actual antecedent | Supply positive lamports for the protected key; bank model protection excludes zero-balance deletion. No runtime persistence law is used to prove this guard. |

### Every remaining P row, owner and exact blocker

Tags: a=frozen3 candidate adoption; b=runtime-law plus contract-game OWNER
clarification; c=session A rows/source interpretation; —=none of those routes.
All implication guards and existential witnesses retain their original joint
scope. New Rc2_P rows apply only to the added bank-model conclusions.

| ID | Scope | Owner | Law family | Exact blocker | OWNER route |
|---|---|---|---|---|---|
| L083 | actual antecedent | lead | accepted1 | Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem. | — |
| L084 | actual antecedent | lead | accepted2 | Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem. | — |
| L094 | actual antecedent | lead | history.savedAtCommit | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. | b: runtime law + contract-game clarification |
| L095 | actual antecedent | lead | history.loadedAtEntry | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. | b: runtime law + contract-game clarification |
| L096 | actual antecedent | lead | history.noInterveningWrite | Prove protection and version provenance of the actual saved Pool checkpoint across transactions. | b: runtime law + contract-game clarification |
| L097 | actual antecedent | lead | p2prime.binding.proof | Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient. | c: session A source/binding rows |
| L098 | actual antecedent | lead | p2prime.binding.pub | Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient. | c: session A source/binding rows |
| L099 | actual antecedent | lead | entry.parsed | Associate the actual accepted proof with its reached parsed transcript on this pair. | — |
| L110 | actual antecedent | session A | r0.field0 | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L111 | actual antecedent | session A | r0.field4 | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L112 | actual antecedent | session A | r0.add | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L113 | actual antecedent | session A | r0.quarter_run | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L114 | actual antecedent | session A | r0.multiply | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L115 | actual antecedent | session A | r0.evaluate | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L116 | actual antecedent | session A | r1.field0 | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L117 | actual antecedent | session A | r1.field4 | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L118 | actual antecedent | session A | r1.add | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L119 | actual antecedent | session A | r1.quarter_run | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L120 | actual antecedent | session A | r1.multiply | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L121 | actual antecedent | session A | r1.evaluate | Supply the two actual round return/evaluation laws from S3/S5/S9. | c: session A source/binding rows |
| L125 | actual antecedent | session A | hw | Supply the same native newWeights/pair/dot primitive return and its model interpretation. | c: session A source/binding rows |
| L127 | actual antecedent | session A | hp | Supply the same native newWeights/pair/dot primitive return and its model interpretation. | c: session A source/binding rows |
| L128 | actual antecedent | session A | hd | Supply the same native newWeights/pair/dot primitive return and its model interpretation. | c: session A source/binding rows |
| L129 | actual antecedent | lead | hi | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. | c: session A source/binding rows |
| L130 | actual antecedent | lead | hq | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. | c: session A source/binding rows |
| L131 | actual antecedent | lead | read | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. | c: session A source/binding rows |
| L132 | actual antecedent | lead | decoded | Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution. | c: session A source/binding rows |
| L133 | actual antecedent | session A | pairing_S3_S5_S9.round0.boundary | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L134 | actual antecedent | session A | pairing_S3_S5_S9.round0.quarter | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L135 | actual antecedent | session A | pairing_S3_S5_S9.round0.eval | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L136 | actual antecedent | session A | pairing_S3_S5_S9.round1.boundary | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L137 | actual antecedent | session A | pairing_S3_S5_S9.round1.quarter | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L138 | actual antecedent | session A | pairing_S3_S5_S9.round1.eval | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L139 | actual antecedent | session A | pairing_S3_S5_S9.claim | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L140 | actual antecedent | session A | pairing_S3_S5_S9.alpha0 | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L141 | actual antecedent | session A | pairing_S3_S5_S9.alpha1 | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L142 | actual antecedent | session A | pairing_S3_S5_S9.pair | Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra. | c: session A source/binding rows |
| L143 | actual antecedent | session A | matches_S4_S7 | Prove actual S4/S7 matching relation for all selected queries. | c: session A source/binding rows |
| L144 | actual antecedent | session A | semantic_S3_S9.EquationEndpoint.initial | Bind same source semantic/initial/chain/terminal equations from S3/S9. | c: session A source/binding rows |
| L145 | actual antecedent | session A | semantic_S3_S9.EquationEndpoint.chain | Bind same source semantic/initial/chain/terminal equations from S3/S9. | c: session A source/binding rows |
| L146 | actual antecedent | session A | semantic_S3_S9.EquationEndpoint.terminal | Bind same source semantic/initial/chain/terminal equations from S3/S9. | c: session A source/binding rows |
| L147 | actual antecedent | session A | dot_S5 | Prove actual S5 dot product equals the selected opening/accumulator model. | c: session A source/binding rows |
| L148 | actual antecedent | session A | canonical_S3_S4_S5_S9 | Prove same source round/pair/dot/rhs canonical observation roundtrips. | c: session A source/binding rows |
| L151 | actual antecedent | lead | i.data.Functional.map_add | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. | — |
| L152 | actual antecedent | lead | i.data.Functional.map_smul | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. | — |
| L153 | actual antecedent | lead | tr.statement.initFits | Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it. | — |
| L154 | actual antecedent | external | hqueries | Prove total ByteProver query budget in the chosen oracle work model. | — |
| L157 | actual antecedent | lead | canonicalJoin.verifier | Raw canonical accepted source/frozen2 equality, including complete ordered oracle log; RawJ_ owner work is not imported. | a: frozen3 adoption (candidate route; no closure credit) |
| L159 | actual antecedent | lead | StoredCarrierBinding | Identify complete accepted runtime RunView with this same source program and oracle world. | a: frozen3 adoption (candidate route; no closure credit) |
| N001 | actual antecedent | session A | prepareOwner.accepted.variant | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N002 | actual antecedent | session A | prepareOwner.accepted.queries | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N003 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N004 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N005 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N006 | actual antecedent | session A | prepareOwner.accepted.gamma.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N007 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N008 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N009 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N010 | actual antecedent | session A | prepareOwner.accepted.gamma.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N011 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N012 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N013 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N014 | actual antecedent | session A | prepareOwner.accepted.kappa.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N015 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N016 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N017 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N018 | actual antecedent | session A | prepareOwner.accepted.kappa.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N019 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N020 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N021 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N022 | actual antecedent | session A | prepareOwner.accepted.alpha.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N023 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N024 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N025 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N026 | actual antecedent | session A | prepareOwner.accepted.alpha.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N027 | actual antecedent | session A | prepareOwner.accepted.rho.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N028 | actual antecedent | session A | prepareOwner.accepted.rho.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N029 | actual antecedent | session A | prepareOwner.accepted.rho.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N030 | actual antecedent | session A | prepareOwner.accepted.rho.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N031 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N032 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N033 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N034 | actual antecedent | session A | prepareOwner.accepted.semanticAlpha.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N035 | actual antecedent | session A | prepareOwner.accepted.coordinates.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N036 | actual antecedent | session A | prepareOwner.accepted.coordinates.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N037 | actual antecedent | session A | prepareOwner.accepted.coordinates.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N038 | actual antecedent | session A | prepareOwner.accepted.coordinates.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N039 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N040 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N041 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N042 | actual antecedent | session A | prepareOwner.accepted.claim.c0.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N043 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c0.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N044 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c0.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N045 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c1.a | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N046 | actual antecedent | session A | prepareOwner.accepted.claim.c1.c1.b | Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission. | c: session A source/binding rows |
| N047 | actual antecedent | session A | primitiveOwner.basis.s3_s4_mul | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N048 | actual antecedent | session A | primitiveOwner.basis.s3_s4_sub | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N049 | actual antecedent | session A | primitiveOwner.basis.s3_s4_double | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N050 | actual antecedent | session A | primitiveOwner.basis.zero | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N051 | actual antecedent | session A | primitiveOwner.basis.one | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N052 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.value | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N053 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N054 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N055 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N056 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c0.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N057 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N058 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N059 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N060 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_mulE.canonical.c1.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N061 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.value | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N062 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N063 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N064 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N065 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c0.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N066 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N067 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N068 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N069 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s5_addE.canonical.c1.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N070 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.value | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N071 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N072 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N073 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N074 | actual antecedent | session A | primitiveOwner.arithmetic.s3_s4_s9_mulK.canonical.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N075 | actual antecedent | session A | primitiveOwner.m31.multiply | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N076 | actual antecedent | session A | primitiveOwner.m31.double | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N077 | actual antecedent | session A | primitiveOwner.m31.one | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N078 | actual antecedent | session A | primitiveOwner.m31.subtract | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N079 | actual antecedent | session A | primitiveOwner.decoder.decode | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N080 | actual antecedent | session A | primitiveOwner.line | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N081 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N082 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N083 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N084 | actual antecedent | session A | primitiveOwner.line_canonical.c0.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N085 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c0.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N086 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c0.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N087 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c1.a | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N088 | actual antecedent | session A | primitiveOwner.line_canonical.c1.c1.b | Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers. | c: session A source/binding rows |
| N089 | actual antecedent | session A | geoLeaves.point.x | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N090 | actual antecedent | session A | geoLeaves.point.y | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N091 | actual antecedent | session A | geoLeaves.line.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N092 | actual antecedent | session A | geoLeaves.multiply.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N093 | actual antecedent | session A | geoLeaves.double.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N094 | actual antecedent | session A | geoLeaves.one.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N095 | actual antecedent | session A | geoLeaves.subtract.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N096 | actual antecedent | session A | domain.fibre.identity | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N097 | actual antecedent | session A | domain.fibre.bound | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N098 | actual antecedent | session A | domain.point.x | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N099 | actual antecedent | session A | domain.point.y | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N100 | actual antecedent | session A | domain.line.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N101 | actual antecedent | session A | domain.multiply.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N102 | actual antecedent | session A | domain.double.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N103 | actual antecedent | session A | domain.one.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N104 | actual antecedent | session A | domain.subtract.value | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N105 | actual antecedent | session A | geometry.multiply | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N106 | actual antecedent | session A | geometry.one | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N107 | actual antecedent | session A | geometry.inverse | Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary. | c: session A source/binding rows |
| N108 | actual antecedent | session A | prepare_S1.queries | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N109 | actual antecedent | session A | prepare_S1.rho_eq | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N110 | actual antecedent | session A | prepare_S1.rho_canonical.c0.a | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N111 | actual antecedent | session A | prepare_S1.rho_canonical.c0.b | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N112 | actual antecedent | session A | prepare_S1.rho_canonical.c1.a | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N113 | actual antecedent | session A | prepare_S1.rho_canonical.c1.b | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N114 | actual antecedent | session A | prepare_S1.alpha1 | Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding. | c: session A source/binding rows |
| N115 | actual antecedent | lead | tx1_saved | Derive the full Context, Prepared and physical writer encoding equation on this same TX1 run. Cons_Ten proves the accumulator under preparation/read laws but does not prove this complete Vec equation. | c: session A source/binding rows |
| N117 | actual antecedent | external | prefixBound | Provide the source-experiment budget association; no resource/work normalization credit is inferred. | — |
| N118 | actual antecedent | external | choiceBound | Provide the source-experiment budget association; no resource/work normalization credit is inferred. | — |
| L165 | deployment only | lead | shape full semantic/transcript join | Header/shape value installed; full source semantic/transcript association remains in L129-L132 and raw join. | c: session A source/binding rows |
| L166 | deployment only | lead | batch source Result/effects | Installed source batch effects are identified by driver construction; native lowering/adoption/effect association still required. | — |
| L168 | deployment alias | lead | prepare Context/Data binding | Same Context/data/preparation and saved-byte association remains as N preparation laws and tx1_saved; not discharged by state arithmetic. | c: session A source/binding rows |
| L176 | deployment only | session A | S6 native decoded/public transport | Semantic source getters/cuts compose, but native ownership/error/cleanup/adoption remains outside the kernel statement. | c: session A source/binding rows |
| L178 | deployment alias | session A | remaining primitive instances | Covered explicitly by N001-N114 primitive/preparation law leaves; do not add another count for this umbrella. | c: session A source/binding rows |
| L179 | deployment only | lead | library/native frame | NP6 closes Claims-local allocation/ownership/cleanup/frame only. Concrete whole library/native frame, allocator interpretation and source-to-artifact association remain outside that helper scope. | — |
| L180 | deployment alias | lead | history protection / Pool-ASQ8 | L094-L096 remain: owner must clarify the physical two-transaction security game and adopt or replace TwoTransactionLaw; prove ordinary-key eligibility, physical identity, final parent success and source-ordered action association. | b: runtime law + contract-game clarification |
| L181 | deployment only | lead | oracle model order | Complete source Program equality is proved; ordered source-to-frozen2 model event/projection association remains raw L157/GExq work. | a: frozen3 adoption (candidate route; no closure credit) |
| L182 | deployment alias | lead | raw canonical join | Same obligation as literal L157 at this installed source, not a second independent gate. | a: frozen3 adoption (candidate route; no closure credit) |
| L185 | deployment alias | lead | deployed stored experiment | Same obligation as literal L159 at this installed source, not a second independent gate. | a: frozen3 adoption (candidate route; no closure credit) |
| L186 | deployment only | lead | source lowering to frozen ELFs | Source-to-SBF/artifact association for the exact frozen ELFs remains; no new binary proof. | — |
| L187 | deployment only | lead | coherent frozen replay | Only coherent cached focused composition audited; full frozen dependency release replay not run. | — |
| L188 | deployment only | lead | final axioms/trust audit | Current top standard-axiom audit passes; final release dependency/trust/adoption audit remains. | — |
| L195 | deployment only | lead | P6Boundary.oracle | Actual native total-oracle/source association remains, distinct from success-only RuntimeSyscall; no P6-boundary binder in this top. | — |
| L196 | deployment only | lead | P6Boundary.binary_parent | Actual native binary-parent callback/log lowering remains a deployment association, not a top antecedent. | — |
| L197 | deployment only | lead | P6Boundary.occupied_parent | Actual native occupied-parent callback/log lowering remains a deployment association, not a top antecedent. | — |
| L198 | deployment only | lead | P6Boundary.sibling_parent | Actual native sibling-parent callback/log lowering remains a deployment association, not a top antecedent. | — |
| L199 | deployment only | lead | P6Boundary.leaf | Actual native leaf callback/source association remains a deployment obligation; no leaf gate binder here. | — |
| Rc2_P001 | actual antecedent | lead | protection.keyLaw | Prove the installed op36 key-equality/source interpretation; adapter remains data-only and arbitrary. Needed for new bank effect/protection conclusions. | — |
| Rc2_P002 | actual antecedent | lead | protection.owner | Associate an arbitrary protected-bank key with the verifier program owner. The accepted writer derives this in its scoped bank model; the top does not identify every arbitrary before/key with that writer. | — |
| Rc2_P003 | actual antecedent | lead | protection.marker.nonempty | Prove nonempty data at the arbitrary protected-bank key; first conjunct of Initialized. Accepted writer shape does not identify the universal before/key. | — |
| Rc2_P004 | actual antecedent | lead | protection.marker.tag | Prove the exact initialized tag at that arbitrary protected-bank key; second conjunct of Initialized. Accepted writer derives its local marker, but this bank/key association remains. | — |
| Rc2_P005 | actual antecedent | lead | protection.positive | Supply positive lamports for the protected key; bank model protection excludes zero-balance deletion. No runtime persistence law is used to prove this guard. | — |

### Validation and remaining boundary

22/60 Lean attempts including dependencies; zero dependency builds, 0/0 Kani.
Final top Rc2_019: exit0, 2.165615717s, 5328524KiB, swap0. Final statement/axiom
audit Rc2_022: exit0, 2.262392340s, 5303300KiB, swap0. Exact target/argv, source
revision/hash, dependency/tool hashes, limits, errors and full #print axioms
are retained per attempt. Six selected theorem audits use exactly
[propext, Classical.choice, Quot.sound]; excluded standalone History also had
standard-only axioms. Nine development failures (002/005/007/008/009/011/014/016/021)
remain excluded. No timeout, memory kill, unchanged failed-source/dependency replay,
cap/heartbeat increase, package replay or launcher/infrastructure edit.
Every compile uses -M7000 and a separate admitted scope with MemoryHigh6G,
MemoryMax8G, MemorySwapMax0, TasksMax64; at most one scope for this job.

Reused pinned coherent SInt2/T2R/Cons/NP6/PoolT/CPP/CPR/CPS dependencies and
NP6's source/Kani certificate; no new native proof or frozen dependency release
rebuild. No shipped/cfg(kani) file changed: the three-ELF rebuild trigger did
not fire. Inherited pins, not freshly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No wallet/key/account cleanup, release-scope change, foreign module change or
push. Next deliverables are the owner decisions above, same saved-Vec/Context
and source/model bindings, concrete primitive instances, then source/artifact
association and coherent release audit. The 100-bit target remains open.

## Recount on Rc3_Top (2026-10-26)


Target not yet established. Counted theorem: `AspisR1.Rc3_Top.deployed`.
This applies Ledger_003–005's atomic quantified-law method, rather than counting
outer binders. Shared cuts/run/parsed values, same existential successors,
conditional guards and common dictionaries are preserved and deduplicated.
Classification and row correspondence are reviewed judgments; enumeration,
field extraction, row diff and totals are mechanical, not a logical solver.

Fresh kernel evidence: Rc3_009 before/after/full Result; Rc3_010–020 SDK/std/
allocator/extraction/entry/hash/child/cut/history/other-cone/RoundValues fields.
Changed literal/finish/remaining nested field expansions reuse SAP_101 and
Rc2_022, whose source/object pins were independently checked. No unrun audit
receives credit. Exact source binders are in the committed module snapshots;
they retain names even where pretty printing uses implications. 677 inherited
source hashes and98 inherited objects are unchanged; no full package replay.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
| actual antecedent | 82 | 113 | 0 | 18 | 92 | 85 |
| deployment only | 6 | 13 | 0 | 12 | 1 | 6 |
| deployment alias | 0 | 4 | 0 | 3 | 1 | 0 |
| all retained audit rows | 88 | 130 | 0 | 33 | 94 | 91 |
| deduplicated actual plus non-alias deployment | 88 | 126 | 0 | 30 | 93 | 91 |

| Scope / owner | T | P | C |
|---|---:|---:|---:|
| actual antecedent / lead | 0 | 18 | 0 |
| actual antecedent / session A | 0 | 92 | 0 |
| actual antecedent / external | 82 | 3 | 0 |
| deployment only / lead | 0 | 12 | 0 |
| deployment only / session A | 0 | 1 | 0 |
| deployment only / external | 6 | 0 | 0 |
| deployment alias / lead | 0 | 3 | 0 |
| deployment alias / session A | 0 | 1 | 0 |
| deployment alias / external | 0 | 0 | 0 |
| all retained audit rows / lead | 0 | 33 | 0 |
| all retained audit rows / session A | 0 | 94 | 0 |
| all retained audit rows / external | 88 | 3 | 0 |
| deduplicated actual plus non-alias deployment / lead | 0 | 30 | 0 |
| deduplicated actual plus non-alias deployment / session A | 0 | 93 | 0 |
| deduplicated actual plus non-alias deployment / external | 88 | 3 | 0 |

Before Rc2: actual82T+171P; strict compatible after:82T+125P;
actual-source after:82T+113P. The inherited security slice excludes the five
Rc2 bank-protection guards:82T+166P →82T+108P. Those five guards are retained,
not newly added by Rc3. Actual P ownership: lead23→18, sessionA145→92,
external3→3. T remains82 external. No new trust/Prop-law family substitutes
for removed rows. No C discharge or percentage claim.

SAP's46 strict Session A claim checks: N001–N046 are supplied by the installed
prepare owner; Rc3_CompatibleTop keeps the exact Rc2 conclusion. Its53 claim
also checks AT THE ACTUAL SAMPLER specialization: N108–N114 add7 Session A
rows, and L129–L132/N115 remove5 lead rows, total58 actual P families. This
is not a58-row weakening of the old universal arbitrary-q/tr/data/rho/Context
continuation. Frozen params/read-observation/parser/Claims removals already
in Rc2 get zero new credit. L151–L153 intrinsic model-carrier laws remain
conservatively inventoried; existential specialization is no arbitrary source
arithmetic theorem.

Reporting correction to SAP's "deployment/aliases unchanged": L168 is an
obsolete alias of the now-derived actual prepare/data/Context/saved-Vec
families. Rc3 retires that alias too, without increasing the58 independent
actual-family delta or changing deduplicated totals. L165 remains PARTIAL:
local source sampler/parser/data join is derived, global raw/event transport
remains. Row-by-row diff for EVERY Rc2 retained row: Rc3_premises.json.diff;
remaining P owner/scope/blocker table: Rc3_REMAINING.md.

| Remaining actual Session A family | Count | IDs |
|---|---:|---|
| pairing_S3_S5_S9 | 10 | L133, L134, L135, L136, L137, L138, L139, L140, L141, L142 |
| r0 RoundValues | 6 | L110, L111, L112, L113, L114, L115 |
| r1 RoundValues | 6 | L116, L117, L118, L119, L120, L121 |
| semantic_S3_S9 | 3 | L144, L145, L146 |
| matches_S4_S7 | 1 | L143 |
| dot_S5 | 1 | L147 |
| canonical_S3_S4_S5_S9 | 1 | L148 |
| hw/hp/hd return equations | 3 | L125, L127, L128 |
| primitiveOwner | 42 | N047, N048, N049, N050, N051, N052, N053, N054, N055, N056, N057, N058, N059, N060, N061, N062, N063, N064, N065, N066, N067, N068, N069, N070, N071, N072, N073, N074, N075, N076, N077, N078, N079, N080, N081, N082, N083, N084, N085, N086, N087, N088 |
| geoLeaves | 7 | N089, N090, N091, N092, N093, N094, N095 |
| domain | 9 | N096, N097, N098, N099, N100, N101, N102, N103, N104 |
| geometry | 3 | N105, N106, N107 |
| prepare_S1 | 0 | none |

The requested finish families sum28 (pairing10, rounds12, semantic3, matching1,
dot1, canonical1); hw/hp/hd are3 further primitive return equations. Binding
families sum61 (primitiveOwner42, geoLeaves7, domain9, geometry3, prepare_S1=0).
Thus28+3+61=92 actual Session A families. The non-alias S6 deployment rowL176
is separate; L178 is the remaining Session A umbrella alias, not an extra
independent primitive gate. Original family owners stay session A even where
individual source cones are S3/S4/S5/S7/S9; this job does not reassign them.


### SAQ_ source-selected candidate, 2026-10-26 (not integrated)

The actual generic `AspisR1.Rc2_Top.deployed` is unchanged: **literal actual-top
delta 0**. `AspisR1.SAQ_CompleteTop.deployed` is a checked source-selected
replacement at `SAQ_CompleteInstall.configuration indexError c reservation`.
It discharges the following Rc2 atomic P leaves, including the guards nested
inside the returned continuation. Do not subtract these from the generic
Rc2 totals until the lead integrates this dictionary and strengthened result.

| Session A owner | Rc2 rows | Selected-instance P leaves removed |
|---|---|---:|
| Query SessionAPrimitives, including decoder, line and line_canonical | N047–N088 | 42 |
| GeometryCanonical.SessionAPrimitives | N089–N095 | 7 |
| Domain.SessionADomain | N096–N104 | 9 |
| Explicit geometry mul/one/inverse equations | N105–N107 | 3 |
| Total | N047–N107 | 61 |

By the Rc2 recount method (atomic conjuncts, quantified families counted once,
shared-dictionary deduplication, unchanged witness/guard correspondence):
actual antecedents 82T+171P → 82T+110P; actual plus non-alias deployment
88T+184P → 88T+123P; all retained audit rows 88T+189P → 88T+128P.
Actual Session A leaves 145 → 84; deduplicated actual/deployment 146 → 85.
These are **selected-instance candidate counts**. T/C deltas are zero.
`indexError : CoreError` is new data choosing the source IndexOutOfRange
constructor in the existing carrier; it is not a correctness-law premise.
The theorem does not prove arbitrary callback dictionaries satisfy these laws.

`SAQ_Forget.result` erases the strengthened outcome to the original Rc2
outcome with the same f/s/outer/pre/middle/fs/ss/run/tx2 witnesses. No new
source hypothesis is needed for erasure. SessionAPrepare remains for SAP_.
The extraction/native/P6/source-to-ELF boundaries, including L178, remain.
The inherited Rc2 frozen2 headline is preserved; adoption of owner-approved
frozen3 still requires integration. No full S2, release or 100-bit claim.

Non-vacuity: `SAQ_Nonvacuity.contracts` derives the three owner contracts for
every input configuration/error value; constructor examples accept index 0
and reject 262144, and source inverse succeeds at 1. This does not construct
an entire accepted native two-transaction execution.

All 100/100 Lean compile attempts are terminal; 0/20 Kani runs. Final audit
SAQ_107: exit 0, 4.960137286 seconds, peak RSS 5308064 KiB, swap 0,
source revision 33f52eda6f7dbc8d85a293119bd4bae6050052c4 plus the pinned
SAQ_Audit source snapshot. Axioms: propext, Classical.choice, Quot.sound.
Each host compile used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64 and -M7000; no timeout/memory kill or package replay.
No shipped source changed and no ELF rebuild was triggered; historical ELF
pins are inherited, not freshly reproduced.

Full before/after printed statements, exact per-attempt commands/revisions,
source/tool/object hashes, failed attempts, resource receipts, recount and
source association limits: [SAQ handoff](../evidence/sessa-prim-20261026/SAQ_HANDOFF.md).

## Recount on Rc4_Top (2026-10-26)


**S2 OPEN; target not yet established.** Counted actual theorem:
`AspisR1.Rc4_Top.deployed` (022; final audit059), with transparent complete
conclusion `Rc4_Statement.Conclusion`. Before/after kernel statements are
028–034/039, complete source binders in the corresponding committed modules.

Ledger_003–005 method: atomic conjunctive leaves; each universally quantified
law family counted once; shared dictionaries, guards and existential witnesses
remain shared. Classification and correspondence are reviewed judgments;
field extraction, enumeration, row diff and sums are mechanical. No security
percentage, outer-binder count, or logical-solver claim.

| Scope | Rc3 T | Rc3 P | Rc4 T | Rc4 P | Rc4 C |
|---|---:|---:|---:|---:|---:|
| actual antecedent |82|113|82|49|0|
| deployment only |6|13|6|13|0|
| deployment alias |0|4|0|3|0|
| all retained audit rows |88|130|88|65|0|
| deduplicated actual plus non-alias deployment |88|126|88|62|0|

| Scope / owner | T | P | C |
|---|---:|---:|---:|
| actual / lead |0|15|0|
| actual / session A |0|31|0|
| actual / external |82|3|0|
| deployment only / lead |0|12|0|
| deployment only / session A |0|1|0|
| deployment only / external |6|0|0|
| deployment alias / lead |0|3|0|
| deployment alias / session A |0|0|0|
| deployment alias / external |0|0|0|
| deduplicated actual+deployment / lead |0|27|0|
| deduplicated actual+deployment / session A |0|32|0|
| deduplicated actual+deployment / external |88|3|0|
| all retained / lead |0|30|0|
| all retained / session A |0|32|0|
| all retained / external |88|3|0|

Actual independent delta: **64 P**, comprising61 session A +3 lead;
no new T/P/C law family. The security slice excluding the five inherited
bank-protection guards changes82T+108P →82T+44P. The five guards are retained.
All original Rc3 rows have a removed/retained entry in `Rc4_premises.json.diff`.
Every remaining P has owner, exact family, blocker and coverage tag in
`Rc4_REMAINING.md`. Tags identify planned coverage, not imported results.

SAQ's61 verified against the actual root/result, not just its candidate:
N047–N088 query42; N089–N095 geometry canonical7; N096–N104 domain9;
N105–N107 mul/one/inverse3. The42 query leaves are5 basis +9 mulE +9 addE
+5 mulK +4 M31 +1 decoder +1 line +8 canonical line leaves.
`Rc4_Assemble` supplies the sole query owner; `Rc4_Cont` and `Rc4_Literal`
supply the six remaining guard families from those exact source bodies.
The61 leaves are absent as premises of the new result, not repackaged.

TxS's four-row claim verified: N115,L151,L152,L153. **N115 already absent
on Rc3**, hence zero incremental credit; its source-selected SAME saved Vec,
Prepared and model-ten result is retained. L151/L152 are now derived at
`TxS_Carriers.source metadata (typedRows ...)` rather than provided by a
law-bearing Data input. L153 is derived by `Rc4_Model.typed` from raw public
bytes through TxS's checked bound constructor. These3 are model-instance
transport discharges; no native arithmetic result is inferred. Raw-to-typed
surjectivity and reverse transports preserve every old input and full result.
Rc4 additionally exports TxS's full physical saved encoding on the SAME run.

L178 is retired: it aliases N001–N114, all now derived at the installed source
instance. This changes all-retained count by one extra alias, with **zero**
independent/deduplicated discharge credit. L168 remains retired by Rc3.
L178's retirement does not retire source/extraction/artifact association.

## Exact before/after and dictionary scope

Before: Rc3 takes `primitiveOwner` at `Rc3_Install.configuration c reservation`
and returns its source-sampler continuation guarded by query/geometry/domain/
mul/one/inverse contracts, with model law-bearing carriers.
After: Rc4 takes `indexError : CoreError` as constructor DATA, no prepare or
primitive owner; returns all retained root conclusions plus the strengthened
result at `Rc4_Install.configuration indexError c reservation`. It computes
model public/address-fit and matching Data, and supplies all61 laws. The
same f/s/outer/pre/middle/fs/ss/run/tx2 tuple is reused throughout; no separately
existential native execution or model Context is joined.

The dictionary is EXACTLY Rc3 with SAQ's query and geometry installation,
and EXACTLY SAQ with Rc3's source-circle installation (`Rc4_Install.rc3/saq`).
It equals the original Rc3 dictionary iff
`SAQ_Decoder.install c.query = c.query` AND
`SAQ_Constructor.install indexError c.geometry = c.geometry`
(`exact_scope`,001). All other configuration fields are retained relative to
Rc3. SAQ replaces source arithmetic/basis/line/decoder callbacks and the source
geometry/inverse/fibre constructor; the error datum selects the fibre failure
value. The explicit body/slot expansions are056/060 and the upstream source
pin packet. This is a source-instance theorem, not a weakening over arbitrary
callbacks. Deployment does **not** presently instantiate equality to an
arbitrary old seed: the root extraction premise is explicitly specialized to
this dictionary, while its actual native/source-to-ELF/error-constructor
association remains open (L186 and existing extraction/runtime boundaries).
No source substitution is silently attributed to frozen binaries.

## Remaining ownership and non-vacuity

Actual remaining P: lead15, session A31, external3. Session A31 =12 round
return/evaluation laws +3 newWeights/pair/dot return equations +10 pairing
laws +1 matching +3 semantic endpoint +1 dot +1 canonical-observation family.
They retain their original owners; SAF_ coverage receives no closure credit.

All retained P coverage (including aliases): CPH_9; PFin_1; F3X_6; SAF_31;
P6B_5; UNCOVERED13. Deployment aliases included in these numbers are not
independent gates. UNCOVERED includes accepted1/2 event guards, proof/public
P2Prime association, external budgets, S6 native transport, library/native
frame, batch lowering, source-to-ELF and final release gates.

`Rc4_Nonvacuity.contracts` derives all three source-owner contracts for every
seed/error value. `model_surjective`/`data_surjective` preserve all old model
inputs and successful decoder-produced inputs. Four reverse transports
recover the entire original Rc3 result with the SAME witnesses. Rc3's accepted
same-proof/public/tag2/1880-byte input and not-all-reject witness remain in
that result under existing history/P2Prime guards. Historical successful exact
ELF/runtime evidence hashes were rechecked; those executions were not rerun.
This is not joint inhabitation of all runtime/crypto/compatibility hypotheses.
In particular the retained frozen2 exact-log compatibility guard is not
claimed satisfiable for deployment. Frozen3 and RuntimePersistence/game(a–d)
are APPROVED, not awaiting decisions; charged frozen3 integration remains work.

## Validation and frozen boundary

60/60 Lean compiles (52 pass,8 retained excluded diagnostics),0/0 Kani;
no further Lean launches. New Statement/Assemble split replaces default-
heartbeat failures011/012/014;002–004/006/017 were ordinary development errors.
No wall timeout, memory kill, cap increase, unchanged-input rerun, infrastructure
repair or package replay. All host jobs used the unchanged S2W launchers and
reservation barrier, one admitted scope at a time,6G/8G/swap0/tasks64,
-j1 -M7000 -DElab.async=false. No barrier contention/retry occurred.

Focused fresh audits028–060 cover root/conclusion/result/continuation/raw
carriers, all changed and retained field families, trust/extraction/runtime,
finish, history, parser, bank and deployment P6 boundary. Every new theorem's
#print axioms uses only propext/Classical.choice/Quot.sound. Section6 command,
source revision+hash/deps/status/wall/RSS/swap/axioms are in per-attempt receipts.
Top022: exit0,7.1109009819920175s,5376440KiB peakRSS,swap0,
revision90af2a9c9f plus exact dirty source snapshot. Final axioms059:
exit0,6.631484054028988s,5347532KiB,swap0,revision5f026d6155 plus audit snapshot.
The final source/object inventory checks all48 prefix sources and87 direct
objects/companions;1381 inherited source/non-vacuity file checks pass.
This is coherent-cache focused composition, not a fresh frozen release replay.

No shipped or cfg(kani) source changed, so no ELF rebuild trigger. Inherited,
not freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No worktree/candidate owned by session A or another worker was edited. No
running-job result was imported or waited for. No keys or funds were touched.

## Recount on Rc5_Top (2026-10-26)

Counted root: `AspisR1.Rc5_Top.deployed`. Base: `Rc4_Top.deployed`.
This section is NEW and append-only; the preceding ledger is verified against the Rc5 stage-0 byte count and SHA-256. No existing row text is edited. Full machine-readable rows/diff: `evidence/recount5-20261026/Rc5_premises.json`; recount command: `python3 evidence/recount5-20261026/Rc5_recount.py`. Fresh kernel inventories025–060 and exact before/after source/elaborated statements are retained in the same directory.

### Exact theorem and dictionary composition

Rc5 uses the approved frozen3 headline and recorded CPH verifier address. `Rc5_Install.rc4`, `.saf` and `.cph` prove exact definitional compatibility after selecting CPP key/clone, SAQ query/geometry, circle and NP6 together. This does not equate arbitrary unselected dictionaries or prove their native implementations. The retained native/extraction boundary is indexed by this combined dictionary.
`Rc5_Source.source` kernel-checks the source projection of the actual `SAF_Deployed.deployed` proof and four checked root predecessors; unprovided obsolete frozen2 arguments must disappear. `Rc5_Close.from_saf` destructures that source once and retains the SAME f,s,outer,pre,middle,fs,ss,run,tx2 and NP6 contents. It derives Rc4 encoding/raw-carrier facts and constructs CPH history on those cuts, then applies the old acceptance/non-vacuity/caller continuations to that history internally.
`Rc5_ResultForget.forget` gives the exact Rc4 SOURCE outcome on those same witnesses, through the checked literal/continuation/caller reverse transports and SAF universal-return reconstruction. It does not imply the false frozen2 deployment log join or universal protection of arbitrary banks/keys. Protection is specialized to the accepted writer CP; owner, marker, funding, both runtime trace instances and the physical recorder are derived with CPH proofs.
The only new named Prop hypotheses are RuntimePersistence (`CPR_DataPersistence.TwoTransactionLaw`) and game fields(a)–(d). The latter contain eleven expanded clauses, including both state-threaded physical traces. RuntimePersistence adds one external T family. The game is explicitly counted below. Existing accepted native wrappers, P2Prime, FirstEntry, frozen3 raw canonical join, runtime carrier binding and query budgets remain; no additional source-refinement assumption is disguised as runtime trust.
Before/after quantifiers: independent entries become the approved correlated bank-lineage experiment; arbitrary-bank protection becomes protection of its accepted writer; the program is CPH's recorded deployment pin. The headline/runtime/adaptive account experiment use CPH's frozen3/GExq carriers; the second choice consumes actual saved bytes, post-copy heap and final allocator state. No universal equality of GExp and GExq failure events is claimed. Complete source/oracle/deployed-event transport remains open under L157/L159/L165/L181/L182/L185. Target, work metric and numerical constants are unchanged.

### Counts by class and owner

Atomic quantified-law-family method: retain guards and shared witnesses, split conjunction/structure inputs, and do not count an existential output as a caller premise. The fresh unchanged structure inventories are compared byte-for-byte with Rc4's kernel field inventories by the recount script. Classification/correspondence is reviewed; enumeration/diffs/totals are mechanical. No outer-binder count or solver claim.

| Scope | Before T | Before P | After T | After P | After C |
|---|---:|---:|---:|---:|---:|
| actual antecedent | 82 | 49 | 83 | 33 | 0 |
| deployment only | 6 | 13 | 6 | 13 | 0 |
| deployment alias | 0 | 3 | 0 | 2 | 0 |
| deduplicated actual plus non-alias deployment | 88 | 62 | 89 | 46 | 0 |
| all retained audit rows | 88 | 65 | 89 | 48 | 0 |

**All eleven approved game clauses are included in the after P counts.** Actual: **82T+49P →83T+33P** (net P−16,T+1). Removing the game-domain rows only for the implementation-obligation comparison gives **83T+22P +11 game clauses**, not 22 total P. Deduplicated deployment: **88T+62P →89T+46P**; its obligation-only subtotal is89T+35P plus11 game clauses. All-retained includes two remaining aliases and is89T+48P.

| Scope | Lead T/P/C | Session A T/P/C | External T/P/C |
|---|---|---|---|
| actual antecedent | 0/18/0 | 0/12/0 | 83/3/0 |
| deduplicated actual plus non-alias deployment | 0/30/0 | 0/13/0 | 89/3/0 |
| actual excluding approved game domain | 0/7/0 | 0/12/0 | 83/3/0 |
| deduplicated excluding approved game domain | 0/19/0 | 0/13/0 | 89/3/0 |

CPH's requested nine rows are verified absent as antecedents: L094–L096, L180, Rc2_P001–P005. **L180 was already a deployment alias in Rc4**, so this is eight actual P removals plus one retired alias. SAF's nineteen are all actual: L110–L121, L125/L127/L128, L139–L141,L148. Combined: **27 actual P families removed**, one alias retired, eleven game P clauses added, one T family added. No T/C family was discharged.
Finish primitive-return records and return/equality facts are derived existential outputs from the same accepted finish, not renamed law inputs. The three Prepared identities come from the same installed saved-checkpoint reader. Canonicality L148 is unnecessary for accepted forward transport; arbitrary raw canonicality is not asserted. The remaining seven arithmetic laws are round0/round1 boundary,quarter,evaluation and pair; matching,three semantic equations and dot remain, for twelve SAG_ families.

### Complete row diff against Rc4

| Row | Class | Owner | Scope | Change |
|---|---|---|---|---|
| L001 | T | external | actual antecedent | retained |
| L002 | T | external | actual antecedent | retained |
| L003 | T | external | actual antecedent | retained |
| L004 | T | external | actual antecedent | retained |
| L005 | T | external | actual antecedent | retained |
| L006 | T | external | actual antecedent | retained |
| L007 | T | external | actual antecedent | retained |
| L008 | T | external | actual antecedent | retained |
| L009 | T | external | actual antecedent | retained |
| L010 | T | external | actual antecedent | retained |
| L011 | T | external | actual antecedent | retained |
| L012 | T | external | actual antecedent | retained |
| L013 | T | external | actual antecedent | retained |
| L014 | T | external | actual antecedent | retained |
| L015 | T | external | actual antecedent | retained |
| L016 | T | external | actual antecedent | retained |
| L017 | T | external | actual antecedent | retained |
| L018 | T | external | actual antecedent | retained |
| L019 | T | external | actual antecedent | retained |
| L020 | T | external | actual antecedent | retained |
| L021 | T | external | actual antecedent | retained |
| L022 | T | external | actual antecedent | retained |
| L023 | T | external | actual antecedent | retained |
| L024 | T | external | actual antecedent | retained |
| L025 | T | external | actual antecedent | retained |
| L026 | T | external | actual antecedent | retained |
| L027 | T | external | actual antecedent | retained |
| L028 | T | external | actual antecedent | retained |
| L029 | T | external | actual antecedent | retained |
| L030 | T | external | actual antecedent | retained |
| L031 | T | external | actual antecedent | retained |
| L032 | T | external | actual antecedent | retained |
| L033 | T | external | actual antecedent | retained |
| L034 | T | external | actual antecedent | retained |
| L035 | T | external | actual antecedent | retained |
| L036 | T | external | actual antecedent | retained |
| L037 | T | external | actual antecedent | retained |
| L038 | T | external | actual antecedent | retained |
| L039 | T | external | actual antecedent | retained |
| L040 | T | external | actual antecedent | retained |
| L041 | T | external | actual antecedent | retained |
| L042 | T | external | actual antecedent | retained |
| L043 | T | external | actual antecedent | retained |
| L044 | T | external | actual antecedent | retained |
| L045 | T | external | actual antecedent | retained |
| L046 | T | external | actual antecedent | retained |
| L047 | T | external | actual antecedent | retained |
| L048 | T | external | actual antecedent | retained |
| L049 | T | external | actual antecedent | retained |
| L050 | T | external | actual antecedent | retained |
| L051 | T | external | actual antecedent | retained |
| L052 | T | external | actual antecedent | retained |
| L053 | T | external | actual antecedent | retained |
| L054 | T | external | actual antecedent | retained |
| L055 | T | external | actual antecedent | retained |
| L056 | T | external | actual antecedent | retained |
| L057 | T | external | actual antecedent | retained |
| L058 | T | external | actual antecedent | retained |
| L059 | T | external | actual antecedent | retained |
| L060 | T | external | actual antecedent | retained |
| L061 | T | external | actual antecedent | retained |
| L062 | T | external | actual antecedent | retained |
| L063 | T | external | actual antecedent | retained |
| L064 | T | external | actual antecedent | retained |
| L065 | T | external | actual antecedent | retained |
| L066 | T | external | actual antecedent | retained |
| L067 | T | external | actual antecedent | retained |
| L068 | T | external | actual antecedent | retained |
| L069 | T | external | actual antecedent | retained |
| L070 | T | external | actual antecedent | retained |
| L071 | T | external | actual antecedent | retained |
| L072 | T | external | actual antecedent | retained |
| L073 | T | external | actual antecedent | retained |
| L074 | T | external | actual antecedent | retained |
| L075 | T | external | actual antecedent | retained |
| L076 | T | external | actual antecedent | retained |
| L077 | T | external | actual antecedent | retained |
| L078 | T | external | actual antecedent | retained |
| L079 | T | external | actual antecedent | retained |
| L080 | T | external | actual antecedent | retained |
| L081 | T | external | actual antecedent | retained |
| L082 | T | external | actual antecedent | retained |
| L083 | P | lead | actual antecedent | retained |
| L084 | P | lead | actual antecedent | retained |
| L094 | P | lead | actual antecedent | removed |
| L095 | P | lead | actual antecedent | removed |
| L096 | P | lead | actual antecedent | removed |
| L097 | P | lead | actual antecedent | retained |
| L098 | P | lead | actual antecedent | retained |
| L099 | P | lead | actual antecedent | retained |
| L110 | P | session A | actual antecedent | removed |
| L111 | P | session A | actual antecedent | removed |
| L112 | P | session A | actual antecedent | removed |
| L113 | P | session A | actual antecedent | removed |
| L114 | P | session A | actual antecedent | removed |
| L115 | P | session A | actual antecedent | removed |
| L116 | P | session A | actual antecedent | removed |
| L117 | P | session A | actual antecedent | removed |
| L118 | P | session A | actual antecedent | removed |
| L119 | P | session A | actual antecedent | removed |
| L120 | P | session A | actual antecedent | removed |
| L121 | P | session A | actual antecedent | removed |
| L125 | P | session A | actual antecedent | removed |
| L127 | P | session A | actual antecedent | removed |
| L128 | P | session A | actual antecedent | removed |
| L133 | P | session A | actual antecedent | retained |
| L134 | P | session A | actual antecedent | retained |
| L135 | P | session A | actual antecedent | retained |
| L136 | P | session A | actual antecedent | retained |
| L137 | P | session A | actual antecedent | retained |
| L138 | P | session A | actual antecedent | retained |
| L139 | P | session A | actual antecedent | removed |
| L140 | P | session A | actual antecedent | removed |
| L141 | P | session A | actual antecedent | removed |
| L142 | P | session A | actual antecedent | retained |
| L143 | P | session A | actual antecedent | retained |
| L144 | P | session A | actual antecedent | retained |
| L145 | P | session A | actual antecedent | retained |
| L146 | P | session A | actual antecedent | retained |
| L147 | P | session A | actual antecedent | retained |
| L148 | P | session A | actual antecedent | removed |
| L154 | P | external | actual antecedent | retained |
| L157 | P | lead | actual antecedent | changed |
| L159 | P | lead | actual antecedent | changed |
| N117 | P | external | actual antecedent | retained |
| N118 | P | external | actual antecedent | changed |
| L165 | P | lead | deployment only | retained |
| L166 | P | lead | deployment only | retained |
| L176 | P | session A | deployment only | retained |
| L179 | P | lead | deployment only | retained |
| L180 | P | lead | deployment alias | removed |
| L181 | P | lead | deployment only | retained |
| L182 | P | lead | deployment alias | retained |
| L185 | P | lead | deployment alias | retained |
| L186 | P | lead | deployment only | retained |
| L187 | P | lead | deployment only | retained |
| L188 | P | lead | deployment only | retained |
| L189 | T | external | deployment only | retained |
| L190 | T | external | deployment only | retained |
| L191 | T | external | deployment only | retained |
| L192 | T | external | deployment only | retained |
| L193 | T | external | deployment only | retained |
| L194 | T | external | deployment only | retained |
| L195 | P | lead | deployment only | retained |
| L196 | P | lead | deployment only | retained |
| L197 | P | lead | deployment only | retained |
| L198 | P | lead | deployment only | retained |
| L199 | P | lead | deployment only | retained |
| Rc2_P001 | P | lead | actual antecedent | removed |
| Rc2_P002 | P | lead | actual antecedent | removed |
| Rc2_P003 | P | lead | actual antecedent | removed |
| Rc2_P004 | P | lead | actual antecedent | removed |
| Rc2_P005 | P | lead | actual antecedent | removed |
| Rc5_T001 | T | external | actual antecedent | added |
| Rc5_G001 | P | lead | actual antecedent | added |
| Rc5_G002 | P | lead | actual antecedent | added |
| Rc5_G003 | P | lead | actual antecedent | added |
| Rc5_G004 | P | lead | actual antecedent | added |
| Rc5_G005 | P | lead | actual antecedent | added |
| Rc5_G006 | P | lead | actual antecedent | added |
| Rc5_G007 | P | lead | actual antecedent | added |
| Rc5_G008 | P | lead | actual antecedent | added |
| Rc5_G009 | P | lead | actual antecedent | added |
| Rc5_G010 | P | lead | actual antecedent | added |
| Rc5_G011 | P | lead | actual antecedent | added |

### Every remaining P row and coverage

Coverage tags name running-job scope, never imported closure. PFin_ covers parser; F3X_ frozen3 raw/source/runtime transport; SAG_ twelve finish families; P6C_ five deployment rows; JFx_ joint fixture instantiation. JFx_ tags on accepted-event/P2Prime/game conditions do not claim universal premise removal. UNCOVERED is explicit. No concurrent prefix is modified.

| ID | Scope | Owner | Job | Family | Blocker |
|---|---|---|---|---|---|
| L083 | actual antecedent | lead | JFx_ | accepted1 | JFx_ covers joint fixture instantiation of this retained accepted-event/P2Prime condition on the SAME dictionary and game instance; a fixture is not universal discharge of this family. |
| L084 | actual antecedent | lead | JFx_ | accepted2 | JFx_ covers joint fixture instantiation of this retained accepted-event/P2Prime condition on the SAME dictionary and game instance; a fixture is not universal discharge of this family. |
| L097 | actual antecedent | lead | JFx_ | p2prime.binding.proof | JFx_ covers joint fixture instantiation of this retained accepted-event/P2Prime condition on the SAME dictionary and game instance; a fixture is not universal discharge of this family. |
| L098 | actual antecedent | lead | JFx_ | p2prime.binding.pub | JFx_ covers joint fixture instantiation of this retained accepted-event/P2Prime condition on the SAME dictionary and game instance; a fixture is not universal discharge of this family. |
| L099 | actual antecedent | lead | PFin_ | entry.parsed | Associate the actual accepted proof with its reached parsed transcript on this pair. |
| L133 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.round0.boundary | Round0: Configuration.finish.field/add remain abstract, and the actual source View.round0 coefficients are not identified with i.data.p0 by a checked installed primitive/data join. |
| L134 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.round0.quarter | Round0: finish.quarter/mulM have no installed native finite-field refinement at this dictionary; source success supplies the return, not its quarter meaning. |
| L135 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.round0.eval | Round0: finish.polynomial remains abstract; the candidate unrolled-polynomial value theorem uses a different concrete dictionary/carrier and needs an explicit source-byte/model p0 join. |
| L136 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.round1.boundary | Round1: Configuration.finish.field/add remain abstract, and the actual source View.round1 coefficients are not identified with i.data.p1 by a checked installed primitive/data join. |
| L137 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.round1.quarter | Round1: finish.quarter/mulM have no installed native finite-field refinement at this dictionary, including the preceding actual polynomial result as claim. |
| L138 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.round1.eval | Round1: finish.polynomial remains abstract; concrete candidate polynomial semantics are not instantiated at this exact dictionary and model p1. |
| L142 | actual antecedent | session A | SAG_ | pairing_S3_S5_S9.pair | finish.newWeights/pair are abstract. S3 grouped pair-loop invariants and S9 factor semantics need concrete source operation, coefficient-array, challenge and model dual-fold bindings at this dictionary. |
| L143 | actual antecedent | session A | SAG_ | matches_S4_S7 | The retained query ports supply accumulation/line meanings, not the source first-fold -> MatchingSupport.foldWord interpretation and all22 selected match0 equations. S4 indexed/tail zero-scanner equivalence is an SDK zero-byte scan, not this law. |
| L144 | actual antecedent | session A | SAG_ | semantic_S3_S9.EquationEndpoint.initial | The actual semantic first boundary/claim at the same literal parser/view/polynomials is not joined to the source semantic execution. Config.boundaries installs circle only, not this arithmetic endpoint. |
| L145 | actual antecedent | session A | SAG_ | semantic_S3_S9.EquationEndpoint.chain | Nine successive source semantic round equations are not composed with the same EquationEndpoint parsed view/polynomials and challenge sequence. |
| L146 | actual antecedent | session A | SAG_ | semantic_S3_S9.EquationEndpoint.terminal | The terminal source call has not been identified with the exact masked spend terminal on i.decoded and i.data.Y at the same literal transcript. |
| L147 | actual antecedent | session A | SAG_ | dot_S5 | finish.dot is abstract. S5 returned-residue/indexed-source-sum theorems apply to withConcreteDot/finishConcreteField/QRaw, requiring a concrete sourceDot installation, decoder agreement, 64 matching final-message reads and actual accumulator-weight bindings. |
| L154 | actual antecedent | external | UNCOVERED | hqueries | Prove total ByteProver query budget in the chosen oracle work model. |
| L157 | actual antecedent | lead | F3X_ | frozen3 canonicalJoin.verifier | Retained exact frozen3 accepted log join / stored runtime carrier association at the combined selected dictionary. F3X_ must replace the raw join with its charged-collision route and bind the actual experiment, including rejected query prefixes. |
| L159 | actual antecedent | lead | F3X_ | frozen3 StoredCarrierBinding | Retained exact frozen3 accepted log join / stored runtime carrier association at the combined selected dictionary. F3X_ must replace the raw join with its charged-collision route and bind the actual experiment, including rejected query prefixes. |
| N117 | actual antecedent | external | UNCOVERED | prefixBound | Provide the source-experiment budget association; no resource/work normalization credit is inferred. |
| N118 | actual antecedent | external | UNCOVERED | choiceBound | Retained query budget now ranges over actual saved/post-copy heap/final allocator state in approved GExq adaptive second choice; one quantified family, no extra independence assumption. |
| L165 | deployment only | lead | F3X_ | shape full semantic/transcript join | Frozen3 is adopted and numerically composed. Complete physical-source/oracle/model/deployed-event transport is still required; no F3X_ result is imported here. |
| L166 | deployment only | lead | UNCOVERED | batch source Result/effects | Installed source batch effects are identified by driver construction; native lowering/adoption/effect association still required. |
| L176 | deployment only | session A | UNCOVERED | S6 native decoded/public transport | Semantic source getters/cuts compose, but native ownership/error/cleanup/adoption remains outside the kernel statement. |
| L179 | deployment only | lead | UNCOVERED | library/native frame | NP6 closes Claims-local allocation/ownership/cleanup/frame only. Concrete whole library/native frame, allocator interpretation and source-to-artifact association remain outside that helper scope. |
| L181 | deployment only | lead | F3X_ | oracle model order | Frozen3 is adopted and numerically composed. Complete physical-source/oracle/model/deployed-event transport is still required; no F3X_ result is imported here. |
| L182 | deployment alias | lead | F3X_ | raw canonical join | Frozen3 is adopted and numerically composed. Complete physical-source/oracle/model/deployed-event transport is still required; no F3X_ result is imported here. |
| L185 | deployment alias | lead | F3X_ | deployed stored experiment | Frozen3 is adopted and numerically composed. Complete physical-source/oracle/model/deployed-event transport is still required; no F3X_ result is imported here. |
| L186 | deployment only | lead | UNCOVERED | source lowering to frozen ELFs | Bind the combined selected SDK/key/clone/query/geometry/circle/native extraction dictionary to the frozen default/devnet/Pool artifacts; inherited exact-ELF success is not universal source lowering. |
| L187 | deployment only | lead | UNCOVERED | coherent frozen replay | Focused coherent-cache composition only; no full frozen release dependency replay in this task. |
| L188 | deployment only | lead | UNCOVERED | final axioms/trust audit | Rc5 standard-axiom audit is complete; the final release-wide trust/axiom audit remains. |
| L195 | deployment only | lead | P6C_ | P6Boundary.oracle | Actual native total-oracle/source association remains, distinct from success-only RuntimeSyscall; no P6-boundary binder in this top. |
| L196 | deployment only | lead | P6C_ | P6Boundary.binary_parent | Actual native binary-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L197 | deployment only | lead | P6C_ | P6Boundary.occupied_parent | Actual native occupied-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L198 | deployment only | lead | P6C_ | P6Boundary.sibling_parent | Actual native sibling-parent callback/log lowering remains a deployment association, not a top antecedent. |
| L199 | deployment only | lead | P6C_ | P6Boundary.leaf | Actual native leaf callback/source association remains a deployment obligation; no leaf gate binder here. |
| Rc5_G001 | actual antecedent | lead | JFx_ | game.a.consecutive | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G002 | actual antecedent | lead | JFx_ | game.a.entry1 | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G003 | actual antecedent | lead | JFx_ | game.a.entry2 | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G004 | actual antecedent | lead | JFx_ | game.b.bankKey | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G005 | actual antecedent | lead | JFx_ | game.b.publicKey | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G006 | actual antecedent | lead | JFx_ | game.b.noOtherTransaction | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G007 | actual antecedent | lead | JFx_ | game.c.parent | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G008 | actual antecedent | lead | JFx_ | game.d.copy | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G009 | actual antecedent | lead | JFx_ | game.d.actions | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G010 | actual antecedent | lead | JFx_ | game.d.writerTrace | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |
| Rc5_G011 | actual antecedent | lead | JFx_ | game.d.readerTrace | Authorized experiment clause, not an implementation law. JFx_ must jointly inhabit it with ALL retained hypotheses; it is counted here rather than discounted as one structure. |

### Non-vacuity, validation and remaining boundary

`Rc5_Nonrejecting.accepted_input` exports accepted input and non-all-reject under the retained P2Prime on the SAME source result, with history constructed. `Rc5_RuntimeFixture.joint_runtime` reuses the checked joint model witness for ALL NEW game/runtime conditions, both runtime admissions, SDK/std consistency, both successful wrappers and nonempty physical events. Its native functions are local successful stubs; it is not extraction to the installed cryptographic source. `Rc5_DictionaryNonvacuity` checks dictionary contracts and model/data surjectivity. **Joint inhabitation of every retained source/crypto/frozen3 hypothesis remains OPEN (JFx_)**; inherited exact-default-ELF success is separate evidence, not that joint kernel witness.
Budget exhausted:60/60 Lean invocations,54 successful,6 excluded development failures,0/0 Kani. Final root017 and reverse019 pass; final19 theorem axiom lines in audit054 are standard-only (propext,Classical.choice,Quot.sound). Each receipt records exact target/argv,source revision/hash,dependency/tool hashes,exit,wall,RSS,swap and enforced cgroup. One own scope at a time,6G/8G/swap0/tasks64,-j1,-M7000. No cap/depth/heartbeat increase,timeout,memory kill,unchanged failed rerun,package replay or infrastructure change. Fresh field audits are required missing evidence artifacts, not repeated full regressions.
Coherent SInt2 and inherited package/core caches are reused and re-pinned; this is focused composition, not a full frozen-release rebuild. No shipped/cfg(kani) source changed: no ELF rebuild trigger. Inherited pins remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No wallet/key/account cleanup. **S2 OPEN; 100-bit deployed target not yet established.**

## Recount on Rc6_Top (2026-10-26)

**S2 OPEN; target not yet established.** Actual theorem: `AspisR1.Rc6_Top.deployed`. Base: `AspisR1.Rc5_Top.deployed`. This is a new section; all preceding bytes were checked unchanged against `evidence/recount6-20261026/Rc6_ledger_prefix.json`.

Method: fresh kernel `#check @...` / `#print` inventories of the root, nested result/caller/continuation/finish, trust structures, game and runtime dictionary; quantified atomic families, shared witnesses/guards and non-alias dictionary deduplication follow the original ledger. Classification and row-to-field correspondence are reviewed; counts are mechanical. The machine-readable rows, diff and source/log hashes are in `evidence/recount6-20261026/Rc6_premises.json`; expanded structure fields are in `Rc6_field_catalog.json`.

| Scope | Before T/P/C | After T/P/C | Lead T/P/C | Session A T/P/C | External T/P/C |
|---|---:|---:|---:|---:|---:|
| actual antecedent | 83/33/0 | 83/32/0 | 0/17/0 | 0/12/0 | 83/3/0 |
| deployment only | 6/13/0 | 6/8/0 | 0/7/0 | 0/1/0 | 6/0/0 |
| deployment alias | 0/2/0 | 0/2/0 | 0/2/0 | 0/0/0 | 0/0/0 |
| all retained audit rows | 89/48/0 | 89/42/0 | 0/26/0 | 0/13/0 | 89/3/0 |
| deduplicated actual plus non-alias deployment | 89/46/0 | 89/40/0 | 0/24/0 | 0/13/0 | 89/3/0 |
| actual excluding approved game domain | 83/22/0 | 83/21/0 | 0/6/0 | 0/12/0 | 83/3/0 |
| deduplicated excluding approved game domain | 89/35/0 | 89/29/0 | 0/13/0 | 0/13/0 | 89/3/0 |

The actual antecedent delta is **0T, −1P, 0C** (L099); the additional deployment delta is **0T, −5P, 0C** (L195–L199). Deduplicated total: **89T+46P → 89T+40P**, with eleven approved game-domain clauses retained. Excluding those clauses explicitly gives **89T+35P → 89T+29P**. No new premise or trust item is added. The seven SessionAPrepare leaves N108–N114 and parser rows L129–L132 were already absent on Rc5 and receive no duplicate removal credit.

Before: the nested Rc5 caller requires `P2Prime → FirstEntryVerifierConeJoin → ∃ parsed, facts ∧ sites ∧ Rc5_Cont.Outcome`. After: Rc6 requires `P2Prime → ∃ parsed, facts ∧ sites ∧ Rc5_Cont.Outcome`; the same result witnesses additionally carry `PFin_Packet.Facts`, `P6C_OnCuts.SafeBatches` and `P6C_FullBoundary.Facts`. The explicit root binders, frozen3 carrier/game/failure events, query budgets and numerical bounds are unchanged. Full before/after statements are retained in `Rc6_before-statement.lean.txt` and `Rc6_after-statement.lean.txt`.

`Rc6_Result.strengthen` uses the existing Rc5 f/s/run/tx2 and checkpoint version for every addition. `Rc6_Install.parser_base`, `p6_base`, `reconstruct` prove dictionary compatibility; `Rc6_Statements.reverse` transports the entire conclusion back to Rc5 on the same inputs. `Rc6_Equivalent.same_domain` proves relative result-domain equivalence under the retained extraction/oracle premises. `Rc6_Nonvacuity.accepted_input` preserves the conditional accepted input and excludes an always-rejecting driver; it does not instantiate all top premises jointly. JFx_ retains that joint fixture obligation.

P6 removal is accepted-run refinement on the original issued ordered logs plus the defined ideal extension; it is not a universal totality claim about an unissued native syscall. `P6C_CarrierGap.independent` explains why mathematical P6 closure does not remove L166. Frozen3/global source and runtime carrier association remain.

### Row diff against Rc5

| ID | Class | Owner | Scope | Change | Evidence |
|---|---|---|---|---|---|
| L001 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L002 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L003 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L004 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L005 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L006 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L007 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L008 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L009 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L010 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L011 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L012 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L013 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L014 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L015 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L016 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L017 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L018 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L019 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L020 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L021 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L022 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L023 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L024 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L025 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L026 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L027 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L028 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L029 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L030 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L031 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L032 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L033 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L034 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L035 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L036 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L037 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L038 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L039 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L040 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L041 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L042 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L043 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L044 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L045 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L046 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L047 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L048 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L049 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L050 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L051 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L052 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L053 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L054 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L055 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L056 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L057 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L058 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L059 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L060 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L061 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L062 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L063 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L064 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L065 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L066 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L067 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L068 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L069 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L070 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L071 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L072 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L073 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L074 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L075 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L076 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L077 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L078 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L079 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L080 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L081 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L082 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L083 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L084 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L097 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L098 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L099 | P | lead | actual antecedent | removed | Rc6_Caller.from_cut |
| L133 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L134 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L135 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L136 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L137 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L138 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L142 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L143 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L144 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L145 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L146 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L147 | P | session A | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L154 | P | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L157 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L159 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| N117 | P | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| N118 | P | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| L165 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L166 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L176 | P | session A | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L179 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L181 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L182 | P | lead | deployment alias | retained | unchanged atomic family; fresh Rc6 inventories |
| L185 | P | lead | deployment alias | retained | unchanged atomic family; fresh Rc6 inventories |
| L186 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L187 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L188 | P | lead | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L189 | T | external | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L190 | T | external | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L191 | T | external | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L192 | T | external | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L193 | T | external | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L194 | T | external | deployment only | retained | unchanged atomic family; fresh Rc6 inventories |
| L195 | P | lead | deployment only | removed | Rc6_Result.strengthen / P6C_FullBoundary.same_cuts / P6C_Extension.boundary |
| L196 | P | lead | deployment only | removed | Rc6_Result.strengthen / P6C_FullBoundary.same_cuts / P6C_Extension.boundary |
| L197 | P | lead | deployment only | removed | Rc6_Result.strengthen / P6C_FullBoundary.same_cuts / P6C_Extension.boundary |
| L198 | P | lead | deployment only | removed | Rc6_Result.strengthen / P6C_FullBoundary.same_cuts / P6C_Extension.boundary |
| L199 | P | lead | deployment only | removed | Rc6_Result.strengthen / P6C_FullBoundary.same_cuts / P6C_Extension.boundary |
| Rc5_T001 | T | external | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G001 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G002 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G003 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G004 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G005 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G006 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G007 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G008 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G009 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G010 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |
| Rc5_G011 | P | lead | actual antecedent | retained | unchanged atomic family; fresh Rc6 inventories |

### Remaining P coverage

Tags identify covering jobs only; none imports closure from a concurrent branch. JFx_ covers fixture instantiation, not universal discharge of accepted-event/P2Prime/game clauses. `UNCOVERED` means no listed job is credited for that row.

| ID | Owner | Scope | Covering job | Remaining family |
|---|---|---|---|---|
| L083 | lead | actual antecedent | JFx_ | accepted1 |
| L084 | lead | actual antecedent | JFx_ | accepted2 |
| L097 | lead | actual antecedent | JFx_ | p2prime.binding.proof |
| L098 | lead | actual antecedent | JFx_ | p2prime.binding.pub |
| L133 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.round0.boundary |
| L134 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.round0.quarter |
| L135 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.round0.eval |
| L136 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.round1.boundary |
| L137 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.round1.quarter |
| L138 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.round1.eval |
| L142 | session A | actual antecedent | SAG_ | pairing_S3_S5_S9.pair |
| L143 | session A | actual antecedent | SAG_ | matches_S4_S7 |
| L144 | session A | actual antecedent | SAG_ | semantic_S3_S9.EquationEndpoint.initial |
| L145 | session A | actual antecedent | SAG_ | semantic_S3_S9.EquationEndpoint.chain |
| L146 | session A | actual antecedent | SAG_ | semantic_S3_S9.EquationEndpoint.terminal |
| L147 | session A | actual antecedent | SAG_ | dot_S5 |
| L154 | external | actual antecedent | UNCOVERED | hqueries |
| L157 | lead | actual antecedent | F3X_ | frozen3 canonicalJoin.verifier |
| L159 | lead | actual antecedent | SCC_ | frozen3 StoredCarrierBinding |
| N117 | external | actual antecedent | UNCOVERED | prefixBound |
| N118 | external | actual antecedent | UNCOVERED | choiceBound |
| L165 | lead | deployment only | UNCOVERED | shape full semantic/transcript join |
| L166 | lead | deployment only | BEf_ | batch source Result/effects |
| L176 | session A | deployment only | UNCOVERED | S6 native decoded/public transport |
| L179 | lead | deployment only | UNCOVERED | library/native frame |
| L181 | lead | deployment only | UNCOVERED | oracle model order |
| L182 | lead | deployment alias | UNCOVERED | raw canonical join |
| L185 | lead | deployment alias | UNCOVERED | deployed stored experiment |
| L186 | lead | deployment only | UNCOVERED | source lowering to frozen ELFs |
| L187 | lead | deployment only | UNCOVERED | coherent frozen replay |
| L188 | lead | deployment only | UNCOVERED | final axioms/trust audit |
| Rc5_G001 | lead | actual antecedent | JFx_ | game.a.consecutive |
| Rc5_G002 | lead | actual antecedent | JFx_ | game.a.entry1 |
| Rc5_G003 | lead | actual antecedent | JFx_ | game.a.entry2 |
| Rc5_G004 | lead | actual antecedent | JFx_ | game.b.bankKey |
| Rc5_G005 | lead | actual antecedent | JFx_ | game.b.publicKey |
| Rc5_G006 | lead | actual antecedent | JFx_ | game.b.noOtherTransaction |
| Rc5_G007 | lead | actual antecedent | JFx_ | game.c.parent |
| Rc5_G008 | lead | actual antecedent | JFx_ | game.d.copy |
| Rc5_G009 | lead | actual antecedent | JFx_ | game.d.actions |
| Rc5_G010 | lead | actual antecedent | JFx_ | game.d.writerTrace |
| Rc5_G011 | lead | actual antecedent | JFx_ | game.d.readerTrace |

**Release gates:** L187 remains `UNCOVERED`: coherent frozen dependency replay. L188 remains `UNCOVERED`: final release-wide trust/axiom audit. The focused Rc6 standard-axiom check discharges neither release gate. L186 source lowering to the frozen default/devnet/Pool artifacts also remains.

Validation: 100/100 Lean compile attempts (8 proof modules and 92 focused inventories), 0/10 Kani, no package replay. Per-attempt exact target, command, exit, wall time, peak RSS, swap, source revision/hash, dependency fingerprints and axioms are retained under `evidence/recount6-20261026/`. All new top theorems have `#print axioms` using only `propext`, `Classical.choice`, `Quot.sound`. One 6G/8G/Swap0/Tasks64 scope at a time, Lean `-M7000`; no cap increases or timeout/memory-kill reruns. The cache inventory pins 1,726 selected modules; two inherited comment-only source variants are recorded separately. This is focused cache composition, not a fresh frozen-release replay. No shipped file or cfg(kani) harness changed, so the ELF rebuild trigger did not fire.
