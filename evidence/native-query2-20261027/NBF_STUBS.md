# Native caller replacements

Field multiplication replacements and exact natural-spec pairings are in
[LPh_STUBS.md](LPh_STUBS.md). No multiplication equivalence is proved in Kani.

| Replacement | Named discharge / required dependency | Domain and precise credit |
|---|---|---|
| `NBF_context` for `update_residue_row` | `NBB_Row.source`, `NBB_RowTrace.native_result`, `NBB_RowWitness.construct` | Address/arguments/call-count projection only. K002 does not credit row values. Exact row domain is four U64 words in SAME terms phase, four power words<P and basis<P. |
| `NBF_write` for `update_residue_row` | Above, plus `NBF_Read.push` and `NBF_Frame.set_frame` | Every row reply is havoced; K003 checks one selected write and arbitrary other row/limb, metadata unchanged. Phase/read inputs for mathematical values are derived by `NBF_Progress.body`; canonical basis by `NBF_BasisDomain.read_canonical`. |
| `NBF_reduce_reply` for `M31::reduce_u64` | `S8OwnedP6ValueModel.reducer_total`, `value_total_model` | Every U64 input; all canonical replies considered by K011 four-call routing. The unique exact natural modulo value comes from the paired Lean result. This is no new reducer equivalence proof. |
| `NBF_value_reply` for `BatchedWeights::value` | `S8OwnedP6ValueModel.value_total_model`, K011 SAME-row routing, `NBB_Finish.source` | Arbitrary64-row raw vector, i<64, any terms. K013 checks a suffix store; later Enumerate context records SAME owner pointer/index. Whole iterator interpretation remains separate. |
| `NBF_decode_reply` for `weights::field` | **OPEN** NBC/NBE SAME canonical-byte decoder law at direct Port3 op21 | K022 checks one closure iteration's slice[672:800], index and array setter for every canonical reply. It credits no decoder semantics or whole query. |

Native Vec gates use real64-row/capacity64 allocation and arbitrary contents.
The model frame is length-generic; the exact native allocation-capacity law or
capacity independence is still a finding in [NBF_FINDINGS.md](NBF_FINDINGS.md).
No restricted local gate is promoted to an every-caller native bridge.

## Query call-routing replacements: OPEN callee associations

K005 and its excluded broader successors replace opening, dots, inverse,
circle, field decoding, line and accumulate with observations. They are not
callee proofs. Required exact statements are [NBF_QueryDependencies.md](NBF_QueryDependencies.md):

- `NBF_open`: NBA_Opening, SAME frozen proof/reached ordinal and opening832.
- `NBF_dots`: native four_dots on SAME opening/g, canonical producer domains.
- `NBF_inverse`: NBC_Geometry, SAME query inverse row and line_z ordinal.
- `NBF_circle` / `NBF_line`: actual fold expression and direct op17/op16 dictionary.
- `NBF_field`: NBC/NBE SAME canonical128-byte field decode and source selector.
- `NBF_accumulate`: complete native accumulation/row/basis/tail association.

The last item has new model-side `NBF_Accumulate.rows`, `NBF_Advance.accepted`
and `NBF_QueryLoop.from_constructors`; their exact native dictionaries are
still OPEN. Broader native query shapes K014–K017 timed out and are excluded.
No field stub or canonicality assumption hides these outstanding associations.
