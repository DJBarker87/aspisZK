# Packed source/reference correspondence

Current status: three complete native packed VALUES checked directly in Lean;
whole-function P6 equality gates remain pending. No top-premise removal credit. Source hashes and selected-prefix lengths are in FJe_inputs.json.
The exact native function bodies are preserved in the isolated input; omitted
Poseidon functions follow trace_round_constant and are not reached by these calls.
The original field and WideExact bodies are present. No function is stubbed.

| Actual source | Owned reference | Correspondence to check |
|---|---|---|
| external_linear_packed state argument | external(s) argument | Same 16 canonical QM31 cells, not independently existential arrays |
| group=0; group<4; start=4*group | Final reference explicitly constructs groups 0,1,2,3 | Same ordered four groups;earlier traversal variants archived in per-run source snapshots |
| state[start .. start+4] literal reads | Explicit [0..3],[4..7],[8..11],[12..15] reads | Same lane indices |
| external_local_packed -> external_local_packed_raw | Current external reference invokes actual external_local_packed;owned local(input) checked separately in K017 | Same actual leaf;K007 raw and K017 complete local equalities successful,no leaf stub |
| local_packed[group] write | Explicit four-cell local_packed literal | Same group output |
| ZERO.add(p0).add(p1).add(p2).add(p3) | Identical ordered add chain | No reassociation or alternate field arithmetic |
| local_packed.map(value.add(sum)) | Explicit p0.add(sum),p1.add(sum),p2.add(sum),p3.add(sum) | Same addition operands and four outputs |
| leading_pair_packed rate loop | leading o, identical j in 0..RATE loop | SAME z/xor12_z, first eight lanes only |
| external_linear_lazy; full_round_m31_constants INITIAL[0] | Identical unchanged native calls | No opaque replacement or stub |
| full_round_m31_constants_packed INITIAL[1] | m31_packed then external | Same base-cell update, pow5 and external operands |
| interpolated_full_pair_packed local reads 1,9,10 | full s local, same literal reads | Same width16 local array |
| interpolate_three_constant_columns calls | Same unchanged calls, same INITIAL[2,3]/FINAL[0,2,1,3] | Native interpolation remains visible to solver |
| full_round(state,even) | Same unchanged call | Same state/constant operands |
| full_round_packed(first,odd) | qm_packed:identical lane loop then external | Same nonlinear value per lane |

All source canonicality preconditions are x<P per raw limb. Loop unwind18
covers widths16, rate8 and groups4, including loop exit; unwinding checks remain
enabled. Default safety/overflow/undefined-call checks remain enabled. Covers
are included to prevent silent vacuity. No succeeded Kani check is a Lean axiom;
a named P6 bridge requires exact checked context plus the Lean reference proof.

The split bounded context computes rows(input) with the exact four source
coefficient rows and assumes each row limb <7P. FJe_RawReference.row_bounds,
checked013, derives ALL those bounds from arbitrary canonical input limbs.
Thus this is a redundant solver constraint,not an input-domain restriction or
an admitted source-output equation. FJe_RawReference.value and output_bound
check the owned raw formula's field value and <56P reduction range. The pure
unchanged dependency PoseidonExternalPackedAlgebra was missing and compiled012
on the coherent SInt2 selection;no old native packed-proof chain was imported.

K008 and K009 exposed continued whole/group external solver growth. K010 was
REJECTED by Kani before verification because overflow checks are mandatory;
the checked profile is restored and no result from it is used. K011 derives
additional local-result/partial-sum canonical bounds (actual local conversion
029 and existing FIv_NativeValue.add),but still timed out. K012 isolates one
output limb and reuses the SAME actual raw helper inside the owned external
reference;this is a real call,no stub. Lower raw equality K007 and the closed
form013 remain the association for that leaf. No successful whole external
bridge is asserted from these failed/subcomponent runs.

Current native Lean closed forms,with no output-value hypotheses:

- FJe_ExternalPackedValue.value:actual native raw cells,conversion,group loop,
  ordered sum and final four map calls -> packing of literal external linear.
- FJe_LeadingPackedValue.value:actual leading absorption,initial constant rows,
  ordinary first round and final nonlinear input -> preceding external VALUE.
- FJe_FullPackedValue.value:actual local[1,9,10],all six literal constant rows,
  interpolation and full rounds -> preceding external VALUE.

All preserve the SAME typed inputs and actual successful call. Only canonical
input conditions remain;output canonicality is proved. These are direct
standard-axiom symbolic source proofs,not inferred from timed-out Kani checks.
K006/K007/K017 successful equality scopes are raw output2/all4/local complete.
K018-020 use explicit-group reference and distinct split lowbits;none,even if
successful,would establish whole packed output equality by itself. No Kani
bridge axiom or unproved theorem is installed.
