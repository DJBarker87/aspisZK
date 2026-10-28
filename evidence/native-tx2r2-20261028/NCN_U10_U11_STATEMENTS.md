# Exact available statements and NCK integration

**U10 OPEN; U11 OPEN. No full native-to-cohort unit hypothesis is discharged.**

NCK_SKELETON.md is now merged on research (inspection pin in NCN_NCK_MATCH.json).
It explicitly says no `NCK_Lower_Uxx : Prop` placeholders were fabricated. Its
U10/U11 names are audit-table rows, with complete unit statements absent. A Git
search of that pinned research's Lean sources finds neither declaration. There
is therefore no defined `NCK_Lower_U10` or `NCK_Lower_U11` kernel statement to
restate/prove here. This packet supplies exact available statements and OPEN
installation gaps, rather than guessing weaker hypotheses under those names.

The actual NCK_CommonCuts.compose inputs are still OPEN model cuts:

```lean
resumeCut : ops.op18 D cp proof pub .S2 hash = ok (.Ok (p,a))
nextTen : a.next = 10#usize
pendingCut : ops.op10 a.weights.deref = ok (.Ok pending)
queryCut : ops.op6 proof p a g none geometry pending 22#usize = ok (.Ok returned)
```

The helper facts below must NOT be substituted for these whole-call equations.
They do not construct acceptance or independently choose p/a/pending/returned.

## U11 checked kernel statements

The exact selected weight helper totality is `AspisR1.NCN_WeightTotal.weights_total`:

```lean
(bytes : Slice U8) (start : Usize) (weights : alloc.vec.Vec K)
(bound : start.val + 16*weights.val.length ≤ bytes.val.length) :
∃ result, CheckpointBytes4Ops.readWeights bytes start weights = ok result
```

Here K is the SAME AspisR1Stage2 QM31 used by CheckpointBytes4Sections, not a
new carrier. For TX2 size1768/start712/length64, the bound follows from the
existing cursor arithmetic. This is MODEL totality, not a native unit bridge.

`NCN_ReaderTotal.section_total` gives all bounded readList outcomes;
`NCN_WeightErrors.loop_error` transports any first decode error to the actual
mutable model loop for arbitrary prefix/old/suffix. Existing
CheckpointBytes4Weights.loop_success gives exact writeback and retained frame.
NCI_SectionCursor and NCI_ReaderWindows supply every successful cursor/byte
window, without a supplied canonical output equation.

The native clauses available for composition are: raw widths1/4/16 at arbitrary
bounded cursor on valid1768 backing; raw32 at all nine source positions;
arbitrary64-cell native weight iterator step with same-reply writeback/frame/
error suppression; full ten-call semantic transport; and exact header/hash
prefix rejects on arbitrary57607/1880 inputs and arbitrary unequal replies.
Each credited clause has its matched failing control and exact domain in
NCN_U11_BRIDGE.md. K077 is deliberately excluded until its negative control.

The SAME saved account/native input-region correspondence, Vec owner and
allocation/cleanup law, concrete Reader/validator dictionary installation,
full successful resume, actual syscall forwarding and native next10 caller
association are not provided. NCI's generic approved RuntimePersistence law
is imported unchanged; its actual write/load premises are not manufactured.

## U10 checked kernel statements

`AspisR1.NCN_ModelStep.product_write` derives exact checked casts/product/add
and array update for a selected j<4, canonical power/basis limbs and the existing
cadence bound on raw. It REUSES NCI_ResidueWords.product_sum and the actual array
index/update laws. No product or sum result is assumed as an input.

`AspisR1.NCN_Cadence.word_mask/flush` prove on EVERY Usize:

```lean
(terms &&& 3#usize).val = terms.val % 4
(terms &&& 3#usize = 3#usize) ↔ terms.val % 4 = 3
```

`AspisR1.NCN_FoldWord.source_ok` proves, for every U64 x, the exact checked
mask/shift/add expression returns ok with value x%2^31+x/2^31 and value<2^34.
`NCI_ResidueInvariant` supplies the unchanged arbitrary-list induction and
mod-P law. `NCI_FinishCanonical.finish_domains` supplies actual selected model
finish totality, length and per-index canonicality.

The new native local value clause is: for every valid64-row Vec of arbitrary
U64 limbs, arbitrary terms and index<64, the frozen value body returns all four
selected limbs modP. It composes the proved record row contract (K059/K060)
and exact Lean-discharged reducer through the actual caller (K061/K062).
The native initializer clause is ONE iteration on arbitrary64-weight/row
pre-state, exact widening/write and other-row frame (K063/K064).

Native integer product/row association, mutable Vec borrowing, allocation/error
ownership, full finish and parent push/accumulate associations are not supplied.
The SInt2/AdapterRw/U10 dictionary installation is OPEN. No artificial complete
unit theorem or whole-TX2 acceptance proposition is introduced.
