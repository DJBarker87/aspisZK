# NJL compiled root statements and (aq)(2) hypothesis inventory

Target not established. Statements below come from successful scope stdout, not a reconstructed statement. Generic SUPPORT domains never become root premises. `(lookup : Cut)` on214 is the reviewed native lookup transcription admitted by(ai)(5); its bounded weight is supplied by the same-link caller_weight theorem.

## TX1:209 — AspisR1.NJL_ActiveInvocation.source

Permitted input/domain inventory: SAME canonical Selectors.high64 and low16; actual CLOSED selector constructors supply domain. typed SAME selectors/canonicality only; every entered child Result discharged; full statement in L005. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_ActiveInvocation.source : ∀ (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors),
  FIw_ArrayValue.canonical s.high →
    FIw_ArrayValue.canonical s.low →
      ∃ grouped out,
        HighTrace (NJB_ActiveReference.high s) (List.ofFn fun b => b) (fun x => FIq_Native.field.QM31.ZERO) grouped ∧
          LowTrace grouped (NJB_ActiveReference.low s) (List.ofFn fun c => c) FIq_Native.field.QM31.ZERO out ∧
            Canon out ∧ NJB_ActiveReference.reference s = ok out ∧ s.active = ok out
```

## TX1:208 — AspisR1.NJL_ActiveInvocation.source

Permitted input/domain inventory: SAME canonical Selectors.high64 and low16; actual CLOSED selector constructors supply domain. typed SAME selectors/canonicality only; every entered child Result discharged; full statement in L005. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_ActiveInvocation.source : ∀ (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors),
  FIw_ArrayValue.canonical s.high →
    FIw_ArrayValue.canonical s.low →
      ∃ grouped out,
        HighTrace (NJB_ActiveReference.high s) (List.ofFn fun b => b) (fun x => FIq_Native.field.QM31.ZERO) grouped ∧
          LowTrace grouped (NJB_ActiveReference.low s) (List.ofFn fun c => c) FIq_Native.field.QM31.ZERO out ∧
            Canon out ∧ NJB_ActiveReference.reference s = ok out ∧ s.active = ok out
```

## TX1:227 — AspisR1.NJL_AbsorptionInvocation.source

Permitted input/domain inventory: SAME canonical low/fixed/two/eight/nodes and opened16, every canonical word; prepared caches derived internally. SAME typed inputs/canonicality only; every child Result/cache domain/frame and all16 array entries discharged internally. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_AbsorptionInvocation.source : ∀ (low fixed two eight nodes : NQ) (opened : Std.Array NQ 16#usize),
  Canon low →
    Canon fixed →
      Canon two →
        Canon eight →
          Canon nodes →
            FIw_ArrayValue.canonical opened →
              ∃ r p scales ys out,
                NJL_AbsorptionPrologue.Cut ![low, fixed, two, eight, nodes] r p
                    (fun j =>
                      { operation := NJL_AbsorptionPrologue.kind j,
                        left := NJL_AbsorptionPrologue.left ![low, fixed, two, eight, nodes] r j,
                        right := NJL_AbsorptionPrologue.right ![low, fixed, two, eight, nodes] r j })
                    (fun j => r (NJL_AbsorptionPrologue.replyIndex j)) NJL_AbsorptionPrologue.positions p p 7 3 ∧
                  NJL_AbsorptionPrologue.Clauses ![low, fixed, two, eight, nodes] r p ∧
                    List.Forall₂ (Lane scales (NJB_Absorption.cell opened)) indices ↑ys ∧
                      ↑out = ↑ys ∧
                        FIw_ArrayValue.canonical out ∧
                          NJB_Absorption.reference low fixed two eight nodes opened = ok out ∧
                            FIq_Native.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal low fixed two
                                eight nodes opened =
                              ok out
```

## TX1:244 — AspisR1.NJL_OccupancyAssociation.source

Permitted input/domain inventory: SAME canonical input/output occupancy, expected M31 < P and all16 opened canonical; arbitrary occupied, no bit-valued restriction. Only SAME typed inputs/canonicality; Packet is DERIVED, never a hypothesis; all contents printed by L023. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_OccupancyAssociation.source : ∀ (input output : NQ) (expected : U32)
  (opened : Std.Array NQ 16#usize),
  Canon input →
    Canon output →
      ↑expected < FIw_ScalarArithmetic.P →
        FIw_ArrayValue.canonical opened →
          ∃ p,
            NJL_OccupancyPacket.reference input output expected opened = ok (pack p.last) ∧
              FIq_Native.pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal input output expected opened =
                  ok (pack p.last) ∧
                FIw_ArrayValue.canonical (pack p.last)
```

## TX1:247 — AspisR1.NJL_PathAssociation.source

Permitted input/domain inventory: SAME canonical selector and openings.z16/succ_z16; all canonical bit values, no binary restriction. SAME typed inputs/canonicality only; Packet and all clauses derived internally; complete fields and root printed. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_PathAssociation.source : ∀ (selector : NQ) (o : Openings),
  Canon selector →
    FIw_ArrayValue.canonical o.z →
      FIw_ArrayValue.canonical o.succ_z →
        ∃ p,
          NJL_PathPacket.reference selector o = ok (pack p.after) ∧
            FIq_Native.pool_v1.pair_forest_semantic_terminal.path_lanes_literal selector o = ok (pack p.after) ∧
              FIw_ArrayValue.canonical (pack p.after)
```

## TX1:214 — AspisR1.NJL_EndpointRoot.source

Permitted input/domain inventory: SAME genuine frozen link index0..135 and either actual caller side; canonical103-cell scratch and selectorhigh64; binary weight from SAME CLOSED link_weight Result; arbitrary ignored tag. Typed genuine caller inputs/canonicality/binary-domain plus reviewed Lookup.Cut only; no child success/endpoint equation/Run/operation-dictionary input; concrete erased Copy instantiated internally. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_EndpointRoot.source : ∀ (before : State) (s : Selectors) (index : Fin 136) (consumer : Bool)
  (tag weight : U32) (lookup : NJL_EndpointLookup.Cut index consumer),
  (∀ (i : Fin 103), Canon (before i)) →
    FIw_ArrayValue.canonical s.high →
      ↑weight ≤ 1 →
        have g := NJL_EndpointLookup.groupIndex index consumer lookup;
        have p := NJL_EndpointLookup.patternIndex index consumer lookup;
        have high := NJL_EndpointLookup.high s index consumer lookup;
        ∃ first second middle after,
          NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight =
              ok (NJL_EndpointWrites.selected high weight) ∧
            FIq_Native.field.QM31.add (before (NJL_EndpointIndices.weight g))
                  (NJL_EndpointWrites.selected high weight) =
                ok first ∧
              FIq_Native.field.QM31.add (before (NJL_EndpointIndices.pattern p)) high = ok second ∧
                NJL_EndpointCell.Cut before middle (NJL_EndpointIndices.weight g)
                    (NJL_EndpointWrites.selected high weight) first
                    { operation := 1, left := before (NJL_EndpointIndices.weight g),
                      right := NJL_EndpointWrites.selected high weight }
                    1 ∧
                  NJL_EndpointCell.Cut middle after (NJL_EndpointIndices.pattern p) high second
                      { operation := 1, left := middle (NJL_EndpointIndices.pattern p), right := high } 1 ∧
                    reference before s index consumer lookup tag weight = ok after ∧
                      (∀ (i : Fin 103), Canon (after i)) ∧
                        ∀ (i : Fin 103),
                          decode (after i) =
                            if i = NJL_EndpointIndices.weight g then decode (before i) + decode high * ↑↑weight
                            else
                              if i = NJL_EndpointIndices.pattern p then decode (before i) + decode high
                              else decode (before i)
```

## TX1:219 — AspisR1.NJL_PatternRoot.source

Permitted input/domain inventory: SAME canonical values4, pattern_selectors26 and patterns14; arbitrary initial four-cell state. Typed same input arrays/canonicality only; both inner/outer traces and every child Result derived internally; complete sparse-dot meaning, no endpoint/Run/operation-dictionary input. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_PatternRoot.source : ∀ (values : Std.Array NQ 4#usize) (weights : Std.Array NQ 26#usize)
  (terms : Std.Array NQ 14#usize),
  FIw_ArrayValue.canonical values →
    FIw_ArrayValue.canonical weights →
      FIw_ArrayValue.canonical terms →
        ∃ after,
          NJL_PatternOuter.Trace (patterns terms) (selectors weights) (List.ofFn fun g => g) (state values) after ∧
            NJB_PatternArray.reference values weights terms = ok (pack after) ∧
              FIw_ArrayValue.canonical (pack after) ∧
                ∀ (g : Fin 4),
                  decode (state (pack after) g) =
                    decode (state values g) +
                      NJL_PatternMeaning.dot (fun i => decode (patterns terms i))
                        (fun i => decode (selectors weights i)) g
```

## TX1:216 — AspisR1.NJL_TagRoot.source

Permitted input/domain inventory: SAME canonical Selectors.high64; coordinate<30; scratch arbitrary and ignored in deployed217. Canonical same inputs only; registry, loop schedule, every raw product/reduction Result, actual full4word constructor and child216 internally discharged; no Run or endpoint equality premise. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_TagRoot.source : ∀ (s : Selectors) (c : Fin 30),
  FIw_ArrayValue.canonical s.high →
    ∃ after,
      reference s c = ok (NJB_Words.value after) ∧
        NJL_TagSchedule.Schedule (NJL_TagData.indices c) (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) ∧
          NJL_TagChunks.Trace s (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) zero after ∧
            Canon (NJB_Words.value after) ∧
              decode (NJB_Words.value after) = NJL_TagMeaning.model s (NJL_TagData.indices c)
```

## TX1:217 — AspisR1.NJL_TagForward.source

Permitted input/domain inventory: SAME canonical Selectors.high64; coordinate<30; scratch arbitrary and ignored in deployed217. Canonical same inputs only; registry, loop schedule, every raw product/reduction Result, actual full4word constructor and child216 internally discharged; no Run or endpoint equality premise. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_TagForward.source : ∀ (scratch : Slice NQ) (c : Fin 30) (s : Selectors),
  FIw_ArrayValue.canonical s.high →
    ∃ after,
      reference scratch c s = ok (NJB_Words.value after) ∧
        Cut s s (↑c) (↑c) 1 (NJB_Words.value after) (NJB_Words.value after) ∧
          NJL_TagChunks.Trace s (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) NJL_TagRoot.zero after ∧
            Canon (NJB_Words.value after) ∧
              decode (NJB_Words.value after) = NJL_TagMeaning.model s (NJL_TagData.indices c)
```

## TX1:231 — AspisR1.NJL_SharedRoot.source

Permitted input/domain inventory: Deployed N33/start49 only; SAME canonical packed24/values33/selector. Only same input canonicality; pack/mul/add Results internally discharged; actual cohort weighted array constructed internally from same33actual products; full raw array equality to adopted add_preweighted. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_SharedRoot.source : ∀ (packed : Std.Array NQ 24#usize) (values : Std.Array NQ 33#usize)
  (selector : NQ),
  FIw_ArrayValue.canonical packed →
    FIw_ArrayValue.canonical values →
      Canon selector →
        ∃ weighted after,
          (∀ (i : Fin ↑33#usize), FIq_Native.field.QM31.mul selector (cell values i) = ok (cell weighted i)) ∧
            reference packed values selector = ok (array after) ∧
              NJL_SharedTrace.Trace (cell values) selector (List.finRange 9) (cell packed) after ∧
                FIq_Native.pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize weighted =
                    ok (array after) ∧
                  FIw_ArrayValue.canonical (array after) ∧
                    ∀ (j : Fin ↑24#usize),
                      FIw_ArrayValue.decoded (array after) j =
                        FIw_ArrayValue.decoded packed j +
                          FIx_SelectedMeaning.contribution (fun i => decode selector * FIw_ArrayValue.decoded values i)
                            49 ↑j
```

## TX1:228 — AspisR1.NJL_OccupancyParent.source

Permitted input/domain inventory: SAME canonical packed24, selectors.high64/low16 and openings.z16; variant arbitrary typed enum. No child success/output/Run/Ops premise; row213 at1017/1018, variant265, occupancy244 and preweighted230 all derived internally at SAME actual source args; all24final cells. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_OccupancyParent.source : ∀ (packed : Std.Array NQ 24#usize) (pub : Public) (o : Openings)
  (s : Selectors),
  FIw_ArrayValue.canonical packed →
    FIw_ArrayValue.canonical s.high →
      FIw_ArrayValue.canonical s.low →
        FIw_ArrayValue.canonical o.z →
          ∃ p,
            pair_forest_semantic_terminal.add_occupancy_lanes packed pub o s = ok p.after ∧
              Cut p.input p.output (NFQ_StatementLaws.expected pub.variant) o.z (NJL_OccupancyPacket.pack p.lanes.last)
                (NJL_OccupancyPacket.pack p.lanes.last) p.after p.after p.input p.output
                (NFQ_StatementLaws.expected pub.variant) o.z 4 1017 1018 0
```

## TX1:229 — AspisR1.NJL_PathParent.source

Permitted input/domain inventory: SAME canonical packed24, high64/low16 selectors, openings.z16/succ_z16; arbitrary xor12_z is unused. Only actual canonical inputs; sum_high57..63, four low reads1/5/9/13, three actual adds and SAME high*low product, child247 and add_preweighted230 at32 all internally derived; all24final cells. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.

```lean
theorem AspisR1.NJL_PathParent.source : ∀ (packed : Std.Array NQ 24#usize) (o : Openings) (s : Selectors),
  FIw_ArrayValue.canonical packed →
    FIw_ArrayValue.canonical s.high →
      FIw_ArrayValue.canonical s.low →
        FIw_ArrayValue.canonical o.z →
          FIw_ArrayValue.canonical o.succ_z →
            ∃ p,
              pair_forest_semantic_terminal.add_path_lanes packed o s = ok p.after ∧
                ∃ events,
                  Cut s p.selector events o o (NJL_PathPacket.pack p.lanes.after) (NJL_PathPacket.pack p.lanes.after)
                    p.after p.after 3 4 32 57 63
```
