# PCXL_ recount by STATUS classes (P6i)

Script: PCXL_recount.py (stdlib, reads committed files with `git show research:`; run from the worktree root:
`python3 -I evidence/prov-p6i-20261110/PCXL_recount.py --out evidence/prov-p6i-20261110/PCXL_COUNTS.json`). No Lean, no extraction, no host.

Result (baseline 1070/572/65, rows 114 reproduced exactly, then 13 job adapters in merge order; P5e at research 4c429d30f4a, P3y (PCWG_, a88d61b8935) last):
**settled 1150 / not settled 420 / other 137 of 1707; rows settled-only 122 of 599.**
After P5e (before P3y): 1143/437/127, rows 120.
P3y: 33 items, only lead_class EQUALITY_PROVED settled (7: NEG_PushActual power_limb_at, residue_limb_at, update_residue_row_loop0 and .body; NGD_AtG.shape; NGD_SlotRef.OFF_NODES; NCX required_binding_is_zero); 2 loop-return refinements, 3 type-map refinements, 4 DEPENDS_ON_LIBRARY_TRUST (HM-B for NEG push, per STATUS text), 1 TYPE_ISOMORPHISM are other; 16 stay open. OFF_NODES was not credited by PCWF (its STATUS says "not in the 12"; baseline class RECEIPTED_TEXT_DIFFERS), so there is no double credit and it counts once, here. Delta settled +7, not settled -17, other +10, rows +2 (120 to 122).

Method. One adapter per job maps that job's STATUS records to (gate module|definition, class) with lead_corrections and lead_classes applied. PCQL and PCVX list no per-definition keys, so keys come from their exit-0 standard-axioms `@FRESH = @GATE` theorems (evidence only), limited to the modules their STATUS claims; the class is the STATUS's, and a theorem-shape credit never overrides an other-class key (4 PCVX EQUALITY_DOMAIN keys kept). PCWM Types records are split by source: `=` theorems stay settled, Equiv defs become TYPE_ISOMORPHISM (12). The fix for the earlier error: the 7 Qm31SamplerIndex conditionals are other, and Equiv types are other.

Agreement with the lead's hand counts: after p6h 1096/542/69, rows 120: exact. Differences, all attributed to keys (PCXL_COUNTS.json, difference_attribution):
- p5b: PCWK `AspisV8R19.QuarticFieldSlice|AspisR66Field.field.r23_product_u32_bounded` is GATE_ONLY_HELPER (other) here; the hand counts did not move it (NS -1, other +1 from p5a on).
- p5d: 8 `AspisR1WithdrawalCaller.Funs` keys in PCWM STATUS (5 SETTLED: VALUE_LIMIT, M31.to_le_bytes, 3 constants; 3 CONDITIONAL_ON_BINDING: encode_digest_canonical family). Mine 1130/485/92 vs hand 1125/494/88 (with the r23 key). The hand delta covers only 3 type equalities, 12 Equiv types and 7 conditionals.
- p5e: the hand +11 includes 4 keys settled earlier by PCQL (DotFinish P, reduce, Q.limbs; FinishCandidateExplicitOps closure) and 1 key outside the cone (Stage2 multiproof.Arity). Mine 1143/437/127 vs hand 1142/441/124 is exactly +5 -4 settled, plus the 8 withdrawal keys and r23.
Rows settled-only: 120 at every step from PCVX through P5e, the lead's figure; P3y moves it to 122.

Caveats. PCQL's FinishCandidateExplicitOps closure is outside its STATUS count of 10 (credited from m1b_files; PCWN lists it as settled). PCVZ's job-level HM-B/HM-D statement is applied to its two refinement keys only; the lead should confirm the three equalities use no HM row. HM listings (per row) and per-class lists are in the JSON; no settled key appears in the PCXF trust-naming records. 56 STATUS-derived items are UNMATCHED (PCVX 48, PCWH 8, outside the baseline universe), listed. FieldDerives uses: none recorded per key. Addition (B) was cancelled by the lead (P6j).

## Calling the row computation (for P6j)
```python
import importlib.util
sp = importlib.util.spec_from_file_location('pcxl', 'evidence/prov-p6i-20261110/PCXL_recount.py')
m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m)   # run from the worktree root; prints the chain
m.rows_settled_only_if(keys)            # keys: iterable of cone keys 'module|definition' treated as SETTLED
# -> {'rows_settled_only': int, 'rows': [...], 'baseline_rows': 120}
```
CLI: `--assume-settled keys.json` (JSON list) prints the same count. `m.cls` is the final class map, `m.cone` the 1707 keys, `m.NOTSET`/`m.SET` the class sets. Sanity: all 420 not-settled keys settled gives 257 rows (258 before P3y).

Target not yet established.
