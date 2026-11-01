# Slice S composition continuation

**14/97 composed rows CLOSED, up from 6/97; 0/7 roots CLOSED. Target not yet established.**

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; adopted headline AspisR1.RPx_Deployed.deployed, coherent SInt2 owners. Composition transport is P6/D188 option A RECLASSIFICATION, not trust removal. Approved runtime trust, RuntimePersistence, L154, privacy, two transactions and 100-bit PER-ATTEMPT soundness are unchanged.

The newly closed rows are M31::to_le_bytes, statement_public_common and both canonicality scanners, each in TX1 and TX2. Native bridge/source fields and trust rows are unchanged. NEJ_validate is authoritative; NEJ_ROW_DELTA.json lists the eight new rows.

| Root | Root rows CLOSED | Native root theorem |
|---|---:|---|
| decode_public_statement_box | 0 | Not established |
| validate_pool_v1_pair_forest_terminal_statement_v1 | 0 | Not established |
| encode_pool_v1_pair_forest_terminal_statement_v1 | 0 | Not established |
| reconstruct_asq8_statement | 0 | Not established |
| decode_pool_v1_pair_forest_terminal_request_v1 | 0 | Not established |
| scan_proof_buffer | 0 | Not established |
| emit_result | 0 | Not established |

No native root theorem with the authorized hypothesis list exists in this packet; therefore there is no native root statement or native-root axiom report to present as proved. The six later roots were not started under the binding first-root order. NEJ_STOP_AUDIT.json enumerates all 61 members and the exact native obligation preventing further standalone Lean closure.

## Validator root and retained inner laws

NEE_K052/K053 (unchanged) provide caller support with local logs, full arbitrary child Results and full arbitrary late-output mutation. NEE_ReachedRootModel.result_and_effects is reused without reproving it. Its exact MODEL statement follows; it is not a frozen native-root theorem. The three named child laws remain explicit:

```lean
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (payment_bridge : ∀ a, Call.payment a ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      pay a = NED_ValidatorTrace.payment a)
    (output_lane_bridge : ∀ d, Call.lane d ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      lane d = NBN_FirstByteDependency.lane enc d)
    (late_bridge : ∀ a out, Call.late a out ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      ignore (late a out) = ignore (NBN_LateSummary.run enc a out)) :
    NEE_ValidatorOracle.run pay lane late s =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       (NED_ValidatorTrace.run s).2)
```

Its printed axioms are [propext, Classical.choice, Quot.sound], re-audited in NEJ_L014. Actual payment/output-lane/late child instances, complete selected native frames and exact physical/call-site bindings remain OPEN. The borrowed common-getter shape is still unadmitted despite K038/K039 direct value/frame checks. No desired equality is hidden in a PhysicalInterpretation record.

## New same-execution and frame statements

All statements below are MODEL/emitted lemmas supporting composition. Their full typed hypotheses are shown; none is reported as a native root theorem. NEJ_L014 audits all 17 new top theorems in one focused import closure.

```lean
theorem list_frame {α : Type} (dst src : List α) (start k : Nat)
    (fits : start + src.length ≤ dst.length)
    (outside : k < start ∨ start + src.length ≤ k) :
    (dst.setSlice! start src)[k]? = dst[k]?
```

'NEJ_ArrayFrame.list_frame' depends on axioms: [propext, Quot.sound].

```lean
theorem array_frame {N : Usize} (dst : Array U8 N) (src : List U8) (start k : Nat)
    (fits : start + src.length ≤ N.val)
    (outside : k < start ∨ start + src.length ≤ k) :
    (dst.setSlice! start src).val[k]? = dst.val[k]?
```

'NEJ_ArrayFrame.array_frame' depends on axioms: [propext, Quot.sound].

```lean
theorem run_spec {α : Type} (src dst : Nat → α) (ws : List (Nat × Nat)) (k : Nat) :
    run src dst ws k = if touched ws k then src k else dst k
```

'NEJ_CommonFrame.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem touched_windows (k : Nat) :
    touched windows k ↔ k < 7 ∨ (8 ≤ k ∧ k < 148)
```

'NEJ_CommonFrame.touched_windows' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem common_bytes {α : Type} (src dst : Nat → α) (k : Nat) :
    run src dst windows k =
      if k < 7 ∨ (8 ≤ k ∧ k < 148) then src k else dst k
```

'NEJ_CommonFrame.common_bytes' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem reserved_frame {α : Type} (src dst : Nat → α) (k : Nat)
    (outside : k = 7 ∨ 148 ≤ k) : run src dst windows k = dst k
```

'NEJ_CommonFrame.reserved_frame' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem window_disjoint {α : Type} (src dst : Nat → α) (a n b m k : Nat)
    (inside : b ≤ k ∧ k < b + m) (disjoint : a+n ≤ b ∨ b+m ≤ a) :
    loop src dst a n k = dst k
```

'NEJ_CommonFrame.window_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem result_and_frame (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : TK) (c : C) :
    ∃ result : Array U8 216#usize,
      AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
        out magic (toRawKind kind) (toRawCommon c) = ok result ∧
      result = NBP_CommonBytes.encoded out magic kind c ∧
      ∀ k : Nat, k = 7 ∨ 148 ≤ k → result.val[k]? = out.val[k]?
```

'NEJ_CommonSourceFrame.result_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem array_copy_frame {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val)
    (outside : k < start ∨ start + W.val ≤ k) :
    (dst.setSlice! start src.val).val[k]? = dst.val[k]?
```

'NEJ_ConcreteFrame.array_copy_frame' depends on axioms: [propext, Quot.sound].

```lean
theorem scalar_frame {N : Usize} (dst : Array U8 N) (i : Usize) (v : U8) (k : Nat)
    (different : k ≠ i.val) : (dst.set i v).val[k]? = dst.val[k]?
```

'NEJ_ConcreteFrame.scalar_frame' depends on axioms: [propext].

```lean
theorem encoded_frame (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (c : pool_v1.payment_relation.CommonPublicV1) (k : Nat)
    (outside : k = 7 ∨ 148 ≤ k) :
    (NBP_CommonBytes.encoded out magic kind c).val[k]? = out.val[k]?
```

'NEJ_ConcreteFrame.encoded_frame' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem value_and_frame {State : Type} (d : Array U32 8#usize) (state : State) :
    NEE_CanonicalFrame.run d state = ok (decide (Canonical d),state)
```

'NEJ_ScannerFramed.value_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem width (digest : Array U32 8#usize) : digest.val.length = 8
```

'NEJ_ScannerWidth.width' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem association {α : Type} (dst src : Nat → α) (start offset : Nat) :
    step dst src start offset =
      write dst (start+offset) ((fun k => src (k-start)) (start+offset))
```

'NEJ_WindowStep.association' depends on axioms: [propext].

```lean
theorem iteration {α : Type} (dst src : Nat → α) (start offset count k : Nat) :
    loop (fun j => src (j-start)) dst (start+offset) count k =
      if start+offset ≤ k ∧ k < start+offset+count then src (k-start) else dst k
```

'NEJ_WindowStep.iteration' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem earlier_frame {α : Type} (dst src : Nat → α) (start offset count k : Nat)
    (before : k < start+offset) :
    loop (fun j => src (j-start)) dst (start+offset) count k = dst k
```

'NEJ_WindowStep.earlier_frame' depends on axioms: [propext, Classical.choice, Quot.sound].

```lean
theorem bounds (start width offset : Nat) (within : offset < width)
    (fits : start+width ≤ 216) :
    start+offset < 216 ∧ offset+1 ≤ width ∧ width-(offset+1) < width-offset
```

'NEJ_WindowStep.bounds' depends on axioms: [propext, Classical.choice, Quot.sound].
