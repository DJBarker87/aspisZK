# Printed root statements and hypothesis inventory

## TX1:118 — NJE_ArityPackets.TX1_118

```lean
NJE_ArityPackets.TX1_118 : ∀ {α : Type} (a : multiproof.Arity) (k : U32 → Result α),
  a.bits = (NJA_CohortArity.arity a).bits ∧
    (do
        let b ← a.bits
        k b) =
      k
        (match a with
        | multiproof.Arity.Two => 1#u32
        | multiproof.Arity.Eight => 3#u32)
```

Own domain: Both Arity constructors; complete U32 Result; pure, empty modifies, arbitrary continuation; no batch precondition

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX1:119 — NJE_ArityPackets.TX1_119

```lean
NJE_ArityPackets.TX1_119 : ∀ {α : Type} (a : multiproof.Arity) (k : U32 → Result α),
  a.levels = (NJA_CohortArity.arity a).levels ∧
    (do
        let b ← a.levels
        k b) =
      k
        (match a with
        | multiproof.Arity.Two => 18#u32
        | multiproof.Arity.Eight => 6#u32)
```

Own domain: Both Arity constructors; complete U32 Result; bits on SAME arity; divisors 1/3, no zero; empty modifies

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX1:120 — NJE_ArityPackets.TX1_120

```lean
NJE_ArityPackets.TX1_120 : ∀ {α : Type} (a : multiproof.Arity) (k : Usize → Result α),
  a.width = (NJA_CohortArity.arity a).width ∧
    (do
        let b ← a.width
        k b) =
      k
        (match a with
        | multiproof.Arity.Two => 2#usize
        | multiproof.Arity.Eight => 8#usize)
```

Own domain: Both Arity constructors; complete usize Result; shifts 1/3 below platform width proved; empty modifies

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX1:121 — NJE_ReadPackets.TX1_121

```lean
NJE_ReadPackets.TX1_121 : ∀ (a : Std.Array U32 16#usize) (i : Usize),
  multiproof.index_at a i = AspisR1Stage2.multiproof.index_at a i ∧ multiproof.index_at a i = a.index_usize i
```

Own domain: Every raw U32[16], SAME usize i<16 on native returning domain; Lean also covers OOB fail; immutable complete carrier

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX1:124 — NJE_RootPackets.TX1_124

```lean
NJE_RootPackets.TX1_124 : ∀ {α : Type} (s : MultiproofConeRef.reference.Scratch) (root : Std.Array U8 32#usize)
  (k : Bool → Result α),
  multiproof.root_matches s.val root = ok (decide ((↑s.val)[0]! = root)) ∧
    (do
        let b ← multiproof.root_matches s.val root
        k b) =
      k (decide ((↑s.val)[0]! = root))
```

Own domain: Every raw byte[16][32] and root[32]; SAME first array; pure complete Bool and arbitrary continuation; scratch other fields unrestricted

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX2:084 — NJE_ArityPackets.TX2_084

```lean
NJE_ArityPackets.TX2_084 : ∀ {α : Type} (a : multiproof.Arity) (k : U32 → Result α),
  a.bits = (NJA_CohortArity.arity a).bits ∧
    (do
        let b ← a.bits
        k b) =
      k
        (match a with
        | multiproof.Arity.Two => 1#u32
        | multiproof.Arity.Eight => 3#u32)
```

Own domain: Both Arity constructors; complete U32 Result; pure, empty modifies, arbitrary continuation; no batch precondition

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX2:085 — NJE_ArityPackets.TX2_085

```lean
NJE_ArityPackets.TX2_085 : ∀ {α : Type} (a : multiproof.Arity) (k : U32 → Result α),
  a.levels = (NJA_CohortArity.arity a).levels ∧
    (do
        let b ← a.levels
        k b) =
      k
        (match a with
        | multiproof.Arity.Two => 18#u32
        | multiproof.Arity.Eight => 6#u32)
```

Own domain: Both Arity constructors; complete U32 Result; bits on SAME arity; divisors 1/3, no zero; empty modifies

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX2:086 — NJE_ArityPackets.TX2_086

```lean
NJE_ArityPackets.TX2_086 : ∀ {α : Type} (a : multiproof.Arity) (k : Usize → Result α),
  a.width = (NJA_CohortArity.arity a).width ∧
    (do
        let b ← a.width
        k b) =
      k
        (match a with
        | multiproof.Arity.Two => 2#usize
        | multiproof.Arity.Eight => 8#usize)
```

Own domain: Both Arity constructors; complete usize Result; shifts 1/3 below platform width proved; empty modifies

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX2:087 — NJE_ReadPackets.TX2_087

```lean
NJE_ReadPackets.TX2_087 : ∀ (a : Std.Array U32 16#usize) (i : Usize),
  multiproof.index_at a i = AspisR1Stage2.multiproof.index_at a i ∧ multiproof.index_at a i = a.index_usize i
```

Own domain: Every raw U32[16], SAME usize i<16 on native returning domain; Lean also covers OOB fail; immutable complete carrier

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX2:090 — NJE_RootPackets.TX2_090

```lean
NJE_RootPackets.TX2_090 : ∀ {α : Type} (s : MultiproofConeRef.reference.Scratch) (root : Std.Array U8 32#usize)
  (k : Bool → Result α),
  multiproof.root_matches s.val root = ok (decide ((↑s.val)[0]! = root)) ∧
    (do
        let b ← multiproof.root_matches s.val root
        k b) =
      k (decide ((↑s.val)[0]! = root))
```

Own domain: Every raw byte[16][32] and root[32]; SAME first array; pure complete Bool and arbitrary continuation; scratch other fields unrestricted

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "universally quantified own carriers / arbitrary continuation"}

## TX1:307 — NJE_Pow5Packet.TX1_307

```lean
NJE_Pow5Packet.TX1_307 : ∀ (x : U32) (len : ℕ) (out : U32),
  Cut x (events x) len out → NJA_FieldLaws.pow5_ref x = ok out ∧ ↑out < 2147483647 ∧ ↑↑out = R0P.poseidonPow5 ↑↑x
```

Own domain: SAME canonical M31 x<2147483647; three natural-product emitted replies; scalar complete result, no effects

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJA_Pow5Cut.Cut with emitted SAME replies installed"]}

## TX1:302 — NJE_Mat4Packet.TX1_302

```lean
NJE_Mat4Packet.TX1_302 : ∀ (v : Fin 4 → U32) (len : ℕ) (post : Fin 4 → U32),
  NJA_Mat4Cut.Cut v (events v) len post →
    ∀ (r : Fin 4), ↑(post r) < 2147483647 ∧ ↑↑(post r) = R0P.poseidonMat4 (fun i => ↑↑(v i)) r
```

Own domain: SAME exactly four canonical M31 cells, no five-cell precondition; all four post cells and u62 reducer domains; pure empty external effects

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJA_Mat4Cut.Cut with emitted SAME replies installed"]}

## TX1:123 — NJE_ParentPackets.TX1_123

```lean
NJE_ParentPackets.TX1_123 : ∀ (hashv : Slice (Slice U8) → Digest) (values : Std.Array Digest 16#usize)
  (i : Usize),
  ↑i + 1 < 16 →
    multiproof.occupied_binary_parent (backend hashv) () values i =
      ok (hashv (parts (cell values ↑i) (cell values (↑i + 1))))
```

Own domain: SAME raw byte[16][32], i+1<16, deployed concrete SolanaDigest, exact tag18+two32-byte children, arbitrary runtime reply

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "own carriers and native index bound; retained runtime hashv input for digest helpers"}

## TX2:089 — NJE_ParentPackets.TX2_089

```lean
NJE_ParentPackets.TX2_089 : ∀ (hashv : Slice (Slice U8) → Digest) (values : Std.Array Digest 16#usize)
  (i : Usize),
  ↑i + 1 < 16 →
    multiproof.occupied_binary_parent (backend hashv) () values i =
      ok (hashv (parts (cell values ↑i) (cell values (↑i + 1))))
```

Own domain: SAME raw byte[16][32], i+1<16, deployed concrete SolanaDigest, exact tag18+two32-byte children, arbitrary runtime reply

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "own carriers and native index bound; retained runtime hashv input for digest helpers"}

## TX1:125 — NJE_ParentPackets.TX1_125

```lean
NJE_ParentPackets.TX1_125 : ∀ (hashv : Slice (Slice U8) → Digest) (values : Std.Array Digest 16#usize)
  (i : Usize),
  ↑i < 16 →
    ∀ (sibling : Digest) (left : Bool),
      multiproof.sibling_binary_parent (backend hashv) () values i (Array.to_slice sibling) left =
        ok (hashv (if left = true then parts (cell values ↑i) sibling else parts sibling (cell values ↑i)))
```

Own domain: SAME raw byte[16][32], i<16, sibling exactly32bytes, both left/right orders, concrete deployed SolanaDigest, arbitrary runtime reply

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "own carriers and native index bound; retained runtime hashv input for digest helpers"}

## TX2:091 — NJE_ParentPackets.TX2_091

```lean
NJE_ParentPackets.TX2_091 : ∀ (hashv : Slice (Slice U8) → Digest) (values : Std.Array Digest 16#usize)
  (i : Usize),
  ↑i < 16 →
    ∀ (sibling : Digest) (left : Bool),
      multiproof.sibling_binary_parent (backend hashv) () values i (Array.to_slice sibling) left =
        ok (hashv (if left = true then parts (cell values ↑i) sibling else parts sibling (cell values ↑i)))
```

Own domain: SAME raw byte[16][32], i<16, sibling exactly32bytes, both left/right orders, concrete deployed SolanaDigest, arbitrary runtime reply

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "own carriers and native index bound; retained runtime hashv input for digest helpers"}

## TX1:126 — NJE_ReadPackets.TX1_126

```lean
NJE_ReadPackets.TX1_126 : ∀ (a : Std.Array (Std.Array U8 32#usize) 16#usize) (i : Usize),
  multiproof.value_at a i = AspisR1Stage2.multiproof.value_at a i ∧ multiproof.value_at a i = a.index_usize i
```

Own domain: Every SAME raw byte[16][32], usize i<16 native; complete emitted fail/ok Result; empty modifies; no binary-parent stand-in

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "own carriers and native index bound; retained runtime hashv input for digest helpers"}

## TX2:092 — NJE_ReadPackets.TX2_092

```lean
NJE_ReadPackets.TX2_092 : ∀ (a : Std.Array (Std.Array U8 32#usize) 16#usize) (i : Usize),
  multiproof.value_at a i = AspisR1Stage2.multiproof.value_at a i ∧ multiproof.value_at a i = a.index_usize i
```

Own domain: Every SAME raw byte[16][32], usize i<16 native; complete emitted fail/ok Result; empty modifies; no binary-parent stand-in

(aq)(2): {"NIG_FinishInput_Domain": false, "endpoint_or_success_premises": [], "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": [], "root_inputs": "own carriers and native index bound; retained runtime hashv input for digest helpers"}

## TX1:128 — NJE_WellFrozen.TX1_128

```lean
NJE_WellFrozen.TX1_128 : ∀ (indices : Slice U32) (out : Bool) (calls : ℕ),
  NJE_WellPacket.Cut (↑indices) (NJE_WellPacket.ordered ↑indices) (NJE_WellPacket.domain ↑indices) out calls →
    emitted indices = ok out ∧
      out = decide (AspisR1.OraclePortFrozenOrder.wellFormed (List.map (fun x => ↑x) ↑indices))
```

Own domain: Every raw Slice U32, including empty, overlength, unsorted and out-of-domain inputs; complete Bool Result and zero writes; SAME-slice all boundaries

(aq)(2): {"NIG_FinishInput_Domain": false, "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJE_WellFrozen association/order_all/domain_all; NJE_AllCalls.default_all; NJA_WellIteration/NJA_WellPredicateLaws"]}

## TX2:094 — NJE_WellFrozen.TX2_094

```lean
NJE_WellFrozen.TX2_094 : ∀ (indices : Slice U32) (out : Bool) (calls : ℕ),
  NJE_WellPacket.Cut (↑indices) (NJE_WellPacket.ordered ↑indices) (NJE_WellPacket.domain ↑indices) out calls →
    emitted indices = ok out ∧
      out = decide (AspisR1.OraclePortFrozenOrder.wellFormed (List.map (fun x => ↑x) ↑indices))
```

Own domain: Every raw Slice U32, including empty, overlength, unsorted and out-of-domain inputs; complete Bool Result and zero writes; SAME-slice all boundaries

(aq)(2): {"NIG_FinishInput_Domain": false, "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJE_WellFrozen association/order_all/domain_all; NJE_AllCalls.default_all; NJA_WellIteration/NJA_WellPredicateLaws"]}

## TX1:303 — NJE_LinearPackets.TX1_303

```lean
NJE_LinearPackets.TX1_303 : ∀ (input : State U32) (bs : ℕ → State U32) (sums : Fin 4 → ℕ → ℕ)
  (args : Fin 16 → ℕ) (steps : ℕ → State U32),
  NJE_ExternalStages.Cut input bs sums args steps →
    (∀ (i : Fin 16), args i < 2 ^ 62) ∧
      ∀ (i : Fin 16),
        ↑(steps 16 i) < 2147483647 ∧ ↑↑(steps 16 i) = R0P.poseidonExternalLinear (fun j => ↑↑(input j)) i
```

Own domain: Exact raw M31[16] input and complete Unit/post-state; canonical inputs are admitted and no caller has a stronger requirement. Four disjoint chunks of exactly4; sixteen selected writes, full outside frames

(aq)(2): {"NIG_FinishInput_Domain": false, "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJE_ExternalStages blocks_result/sum_result; NJE_ExternalTotal argument/result; NJE_Mat4Packet domains/laws"]}

## TX1:304 — NJE_LinearPackets.TX1_304

```lean
NJE_LinearPackets.TX1_304 : ∀ (input : NJA_Internal.State) (sums : ℕ → ℕ) (full : ℕ) (args : Fin 16 → ℕ)
  (steps : ℕ → NJA_Internal.State),
  (∀ (i : Fin 16), ↑(input i) < 2147483647) →
    NJE_SumStage.Cut input sums →
      NJE_InternalCut.Cut input (sums 15) full args steps →
        (∀ (i : Fin 16), args i < 2 ^ 62) ∧
          ∀ (i : Fin 16),
            ↑(steps 16 i) < 2147483647 ∧ ↑↑(steps 16 i) = R0P.poseidonInternalLinear (fun j => ↑↑(input j)) i
```

Own domain: Canonical M31[16], exact full state and same captured full_sum; complete Unit/post-state, fifteen-term sum then zero+fifteen selected writes

(aq)(2): {"NIG_FinishInput_Domain": false, "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJE_SumStage.complete/native_domains; NJE_InternalCut args_source/frame_result; NJE_InternalPacket.result; NJE_ConstantShifts.source"]}

## TX1:122 — NJE_CountPacket.TX1_122

```lean
NJE_CountPacket.TX1_122 : ∀ (indices : Slice U32),
  ∃ out,
    source indices = ok out ∧
      Option.map (fun x => ↑x) out =
        if wellFormed (List.map (fun x => ↑x) ↑indices) then some (nodeCount 18 (List.map (fun x => ↑x) ↑indices))
        else none
```

Own domain: Binary Arity::Two; every raw Slice U32, complete Option<Usize> Result including None on failed well_formed; readonly indices, all18 levels, entire mutable local level[16] retained during induction; accepted size<=16 established internally

(aq)(2): {"NIG_FinishInput_Domain": false, "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJE_CountPacket.result/continuation/initial_view; NJE_CountLevels.total; NJE_CountRows.total; NJE_CountGroup.total; NJE_CountInit.result"]}

## TX2:088 — NJE_CountPacket.TX2_088

```lean
NJE_CountPacket.TX2_088 : ∀ (indices : Slice U32),
  ∃ out,
    source indices = ok out ∧
      Option.map (fun x => ↑x) out =
        if wellFormed (List.map (fun x => ↑x) ↑indices) then some (nodeCount 18 (List.map (fun x => ↑x) ↑indices))
        else none
```

Own domain: Binary Arity::Two; every raw Slice U32, complete Option<Usize> Result including None on failed well_formed; readonly indices, all18 levels, entire mutable local level[16] retained during induction; accepted size<=16 established internally

(aq)(2): {"NIG_FinishInput_Domain": false, "extra_logical_hypotheses": [], "headline_hypotheses": [], "reviewed_parent_cuts": ["NJE_CountPacket.result/continuation/initial_view; NJE_CountLevels.total; NJE_CountRows.total; NJE_CountGroup.total; NJE_CountInit.result"]}
