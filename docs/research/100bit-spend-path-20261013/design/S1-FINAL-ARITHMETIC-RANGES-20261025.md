# S1 same-caller final arithmetic ranges, 2026-10-25

**Established:** the SAME conditional original-SDK/source witness now supplies the actual final mask, Terminal return, multiplication, additions, extra[28], and comparison calls, with canonical ranges for mask/product/sum/extra/result. These range conclusions have **no Terminal or eta canonical-input premise** and no independent field-call/mask-success premise. **S1/S6 and the implementation-linked <=2^-100 target remain OPEN.** S2 remains transferred.

## New accepted-product fact

`AspisS1AcceptedProductCanonical.cm_mul_success_canonical` and `qm_mul_success_canonical` prove that a normally returned multiplication in the checked extracted source model is canonical for arbitrary full raw input words. `generated_mul_success_canonical` transports the SAME result through the existing unconditional generated/probe Result equality, including its fail/div behavior. The input carriers are the full CM31/QM31 U32 coordinates; neither a canonical input subtype nor a callback containing the desired postcondition is introduced.

The proof reuses existing field arithmetic results, rather than reproving S5 arithmetic: existing extracted M31 multiplication/reduction canonicality is unconditional; the complete source CM31 graph supplies its own cross-product/reducer/subtraction executions. Their outputs feed the complete QM31 graph, whose subsequent source operations yield canonical components. Every child success is derived from that enclosing normal return. No source field operation or other session's track was modified.

This is **ACCEPTED-ONLY**, not raw-input TOTAL or an unconditional decoded multiplication formula. The checked cross-product failure cases remain part of the implementation model. Existing canonical-input TOTAL/exact arithmetic theorems remain unchanged and are separately reused. Normal cases are nonvacuous: the existing TOTAL theorem supplies normal returns on all canonical operands.

## Actual caller connection

`S1SourceFinalOpsV1` factors the exact complete add/mul definitions from `S1FinishChildrenV1`, and reuses the exact add/mul/final-arithmetic theorem bodies from `S1FinishArithmeticTotalV1`. Carrier maps, errors and source calls are unchanged. The factor avoids importing unrelated circle proofs. Its new `mul_success_canonical` requires only the actual source multiplication return, not canonical operands. Add/mul installation commutes with the existing mask/selector and root-copy installations.

`AspisS1ReachedFinalNumeric.finish_final_numeric` consumes one successful full source finish and its later successful borrowed prepared_claim on the SAME retained semantic witness. It derives:

- The actual selector calls, row0column27 read and mask call, with canonical returned mask.
- The SAME source Terminal call and `eta*terminal` call. The returned product is canonical without assuming Terminal or eta canonicality.
- Both actual source additions and the exact extra[28] read; their canonical inputs and results are derived from the same mask/product/decoder witnesses.
- The actual final false-mismatch guard and the exact additive equation `decode target = decode mask + decode product + decode extra28`.

`verify_final_numeric` derives that finish from the same installed semantic-verifier return; an independently successful prefix/begin/finish is not a caller premise.

The decoded field-product formula is retained honestly as a separate conditional conclusion: if eta and Terminal are canonical, then `decode target = decode mask + decode eta * decode terminal + decode extra28`. The enclosing SDK's unchanged challenge-range conclusion already supplies eta's canonicality; Terminal's domain/meaning is still an outstanding source interface. No such condition is needed for the five numeric output-range conclusions above.

## Enclosing SDK theorem and exact statement change

`AspisS1SdkFinalArithmetic.original_sdk_final_arithmetic` in `S1SdkFinalArithmeticV1.lean` consumes the existing `original_sdk_canonical_mask` theorem at the explicit instance

```
prior base := AspisS1SourceFinalOps.install backend
```

Thus the prior selector/mask installation is retained and add/mul are also fixed to their actual source operations. The new `ReachedFinalNumeric` conjunct identifies the digest, public argument and retained semantic object from that SAME source cut. All original public1880-byte/decode, checkpoint/frame, selected public witness, reused29 gamma powers/scratch, borrowed prepared_claim, serialized joint challenge trace, row31 program and tx1 continuation conclusions are retained.

The materializer/checker compares the complete old/new binder and postcondition text under precisely that dictionary substitution; only the new reached-final-arithmetic conjunct is added. This is a concrete source-instance specialization of the previous free dictionary, not a claimed universal weakening for every possible old dictionary. No SDK/canonical-input/Terminal-range/independent field-success hypothesis is added.

The old local TOTAL theorem required four canonical operands. It is still true and unchanged. The new caller range theorem does not assume those four premises: mask and extra ranges are derived, and the product's accepted-return canonicality removes the need for a Terminal range premise for these output ranges. The stronger multiplicative decoded equation retains its explicitly stated domain. These are different, clearly separated conclusions.

The result describes local values in the checked finish body and uses the prior retained semantic-model witness. It does not assert that this retained type contains or fully maps every additional frozen Rust field. The existing source-to-full-native-carrier/ABI and actual SDK binding obligations remain unchanged.

## Focused validation

All four smallest changed targets passed first try, Lean4.32 with atomic shared local lock, one job, `-j1 -M4400`, warm pinned imports. No resource-option overrides, sorry/custom axioms/native_decide/bv_decide, unchanged full replay or new native/NUC/SBF job. Twelve full axiom reports use only propext/Classical.choice/Quot.sound. No source decision or production modification occurred.

| Target | Exit | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| S1AcceptedProductCanonicalV1 | 0 | 15.585438250 | 2566569984 | 0 |
| S1SourceFinalOpsV1 | 0 | 9.738047416 | 3283648512 | 0 |
| S1ReachedFinalNumericV1 | 0 | 7.687383750 | 3874521088 | 0 |
| S1SdkFinalArithmeticV1 | 0 | 5.098425542 | 3887136768 | 0 |

Total38.109294958 seconds. Exact source revision/snapshots, source/tool/direct-import hashes, commands, exit/wall/RSS/swap, and every axiom report are in `evidence/s126-current-caller-20261021/s1-final-arithmetic-20261025/metrics.json` and the four named attempt directories. Source/proof factor spans are checked byte-for-byte. The prior same-caller mask packet and native selector/source evidence are reused by read-only hash checking, without rerunning their compilers or claiming a fresh native result.

## Remaining obligations

- The original Library/SDK borrow/copy/TrustedStd, allocator, entry/runtime admission, adapter/verifier operations, native first/second, digest extraction, and matching SourceCuts remain the same explicit boundaries at the newly specified source instance. This does not prove existence of an actual matching cut or unconditional frozen SDK execution refinement.
- Other finish interfaces, particularly claims, Terminal and circle, retain their source/native/meaning obligations. The semantic verifier retains the existing concrete root-copy installation. Terminal range is no longer needed for the final output ranges, but its actual computation/semantic meaning and its domain for the stronger decoded product formula are not discharged here.
- The parent result is ACCEPTED-ONLY. Complete arbitrary-input source/R22 totality, native overflow/abort/effect transport, Claims storage/Box union initialization and cleanup, and whole original caller/native binding remain open. The existing canonical-input child TOTAL results are not a proof of arbitrary raw-input TOTAL.
- The original safe Claims candidate891a213f79 remains NOT ADOPTED; its source/equivalence/caller/CU/artifact decisions and re-pins are unaffected. Current/shared context/kernel, oracle/event/probability and release artifact/SBF/CU joins remain with their owners. The authoritative freeze25866ec331cc7ce27dd9956609c11d32fa8fa58a and adopted powers overlay29cbab431742f7e899870595167efa193a379f0a are unchanged.

A Terminal-source owner may reuse `qm_mul_success_canonical` to derive returned-product ranges without assumed operand ranges; this packet makes no new Terminal-source theorem claim. No other live worktree, frozen Rust, artifact, key, security contract, per-attempt metric or grinding accounting was changed.

Read-only source-only packet check: `python3 tools/s1-final-arithmetic-20261025/check.py`. This is not a coherent frozen release replay or a100-bit implementation conclusion.
