# New Kani run plan (not launched)

List the exact harness before charging it. Stop the entire queue on the first
configuration failure. The eight new runs are separate from the historical 12.
No invocation is authorized until the host restoration flag opens the gate,
and the requested pending Lean modules and final audit have run first.

First proposed verification harness:
`pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::pv_srcid3_full_dynamic_mapper`

The harness compares every RW/RP field of the actual full mapper with the
owned dynamic-root reference over arbitrary inputs. Both sides call the actual
pure root helper, with no stubs and unwind 33 plus unwinding assertions. This
matches `PV_Src_RecordDynamic.call` rather than the fixed-root dictionary.
The earlier timed-out full gate compared against a fixed table; no unchanged
failed gate is being rerun. No claim of success follows from this draft.

Expected time: cached optimized proof compilation, then named full mapper
CBMC elimination/symbolic execution. Same 6G/8G/swap0/tasks64 scope and one
scope at a time. Read-only cache/tool availability checks and an exact metadata
harness inventory precede any charge. A missing cache is recorded and rebuilt
only in the authorized task directory from the restored pinned objects/source.
No compilation has run. Remaining seven runs are not precommitted to redundant
projections: choose the next source obligation from the first actual result.

After dynamic-full1 timeout, the named decomposition queue is:

- pv_srcid3_dynamic_transfer: all RW/RP fields, Some recipient branch.
- pv_srcid3_dynamic_withdrawal: all RW/RP fields, None recipient branch.
- pv_srcid3_dynamic_witness: every private field, both branches.
- pv_srcid3_dynamic_public: every public field, both branches.
- pv_srcid3_dynamic_path_cell: every membership level/lane, both branches.

Prefix each with pool_v1::pair_forest_copy_builder::records_proofs::pv_srcid3::.
Metadata is compiled/listed before these five verification charges. All remain
unstubbed/unwind33. First two branches cover every Option recipient. The last
three do not assert stronger full tuple equality individually. Timeout budget
is 120 sec each (same memory caps); no unchanged failed harness is rerun.
