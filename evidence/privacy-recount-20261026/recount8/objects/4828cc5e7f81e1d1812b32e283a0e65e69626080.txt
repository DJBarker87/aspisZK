# D275 extraction boundary — route stopped

Final shipped source revision: `c58e0473ac60090f016a59e3b7953f429de2d5c2`.

The pinned Aeneas run `pv14-records-aeneas-03` exits 2 with:

```
Source: 'crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs', lines 238:15-242:9
Compiler source: interp/InterpBorrows.ml, line 2731
```

The stack enters `simplify_dummy_values_useless_abs_aux` / `visit_ASharedLoan`
while `eval_switch_with_join` joins the tuple-valued sibling branches inside
the indexed while loop. The range `ub_checks<bool>` error is gone.
`pv14-records-aeneas-02` had the same shared-loan error before entry-copying
input; it was not rerun unchanged: the `Copy` repair changed the source.

The LLBC proves both allowed witness copies are retained: locals 7 (`input`)
and 8 (`pair`) are initialized by `Copy` from the parameter and its field.
Nevertheless, implicit array-index shared borrows remain: statement 661 on
`pair.membership.siblings` (239:66), 666 on `input.super_root_directions`
(241:23), and 671 on `input.super_root_siblings` (241:65).
The exact nodes are `branch-borrow-llbc-d275.json`. These are array-index
borrows of owned local copies, rather than a remaining explicit shared witness
binding that kind (i) could replace. There is no closure/combinator or `for`
in this failing span to remove under (ii)/(iii).

The minimal next source-level candidate is to remove the tuple-valued join by
placing the bit and sibling assignments inside each branch. The exact proposed
diff is `UNAPPLIED-branch-proposal-d275.diff`. It preserves the apparent values
and loop order but changes the branch body, rather than performing one of
(i)–(iii), so it is **not applied**. This candidate has not been tested and is
not asserted to cure the extractor; it identifies the next repair requiring
lead authorization. No extractor patch, stub, assumed helper equality, source
signature or other function change is made.

The earlier `raw` FnOnce extraction obstruction outside `records` is retained
in runjoin13 evidence. Raw and empty-root helpers remain opaque in the present
isolation; their concrete links would still be required even if the mapper
emitted. No successful `R_shipped` definition or identification is claimed.

The requested stop is an extraction repair boundary, not a checked ROW
counterexample or exhausted Lean/Kani budget. The final three-ELF build still
runs because it is required after the last shipped source change. No further
proof scope is launched on this stopped route.
