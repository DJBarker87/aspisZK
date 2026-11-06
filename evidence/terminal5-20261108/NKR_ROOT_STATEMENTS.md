# NKR exact printed root statements

These are exact printed theorem types, cut immediately before the proof-term `:=`, from retained focused stdout. The251 and250 rows intentionally use the same composed root. No Lean source or compiled object was changed for this review.

Status: both combined-gate attempts failed; all six packets remain **local-gate-incomplete**, regardless of successful focused compilation or raw axiom reports. No CLOSED or next-ledger credit follows from this document. See NKR_ROOT_HYPOTHESES_REVIEW.md for premise classification and limitations.

## TX1:225

Focused receipt: `NKR_L082`; exit `0`. Exact stdout SHA256 `a48476dddbafc473b751448976c7655e9f26aaa4b78071eabe30146c8d5ad119`.

```lean
theorem AspisR1.NKR_SumCarrier.source : ∀ (l r : A4) (count : ℕ),
  1 ≤ count →
    count ≤ 4 →
      FIw_ArrayValue.canonical l →
        FIw_ArrayValue.canonical r →
          ∃ out,
            native l r count = ok out ∧
              reference l r count = ok out ∧
                Canon out ∧
                  decode out = NGA_SumAlgebra.sumProducts (List.take count ((↑(encode l)).zip ↑(encode r))) ∧
                    ∀ (seek : Fin 4),
                      ↑seek < count →
                        NKR_SumCuts.Cut (encode l) (encode r) count seek (qm out) (qm out)
                          (NGA_Indexed.selected (encode l) seek) (NGA_Indexed.selected (encode r) seek) 1 count
```

## TX1:232

Focused receipt: `NKR_L010`; exit `0`. Exact stdout SHA256 `be90d1a92e668daf829c0201c2e7ceb454980e6e261bd077095f3acedc742bd2`.

```lean
theorem AspisR1.NKR_ScheduleRoot.source : ∀ (packed : Std.Array NQ 24#usize) (p : Public) (o : Openings)
  (s : Selectors),
  canonical packed →
    canonical o.z →
      canonical s.high →
        canonical s.low →
          ∃ l absorption middle out,
            NKI_InitialInvocation.Clauses p o s l ∧
              pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption p o s =
                  ok (l.initial2, absorption) ∧
                pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize l.initial2 = ok middle ∧
                  pool_v1.pair_forest_semantic_terminal.add_preweighted middle 16#usize absorption = ok out ∧
                    NKR_ScheduleCut.Cut packed p o s l.initial2 absorption middle out
                        (NKR_ScheduleCut.observations packed p o s l.initial2 absorption middle out) ∧
                      pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed p o s = ok out ∧
                        canonical out ∧
                          ∀ (j : Fin ↑24#usize),
                            decoded out j =
                              decoded packed j + FIx_SelectedMeaning.contribution (decoded l.initial2) 0 ↑j +
                                FIx_SelectedMeaning.contribution (decoded absorption) 16 ↑j
```

## TX1:251

Focused receipt: `NKR_L168`; exit `0`. Exact stdout SHA256 `7742b4263c3c27b30c332fffe4c33485ddadafba2c88862ce073c273cc01bbd5`.

```lean
theorem AspisR1.NKR_DigestComposed.source : ∀ (p : Public) (o : Openings) (s : Selectors),
  NKR_DigestChildren.Domain p →
    FIw_ArrayValue.canonical o.z →
      FIw_ArrayValue.canonical s.high →
        FIw_ArrayValue.canonical s.low →
          ∃ c sums out old v m,
            NKR_DigestChildren.Clauses p o s c ∧
              NKR_DigestChildren.Canonical c ∧
                NKR_DigestInvocation.PrefixArithmetic c v ∧
                  NKR_DigestPrefixStep.Trace p o s c (List.finRange 4) ![zero, zero, zero] ![zero, v 3, zero] ∧
                    NKR_DigestInvocation.MiddleArithmetic c ![zero, v 3, zero] m ∧
                      NKR_DigestCuts.MiddleNative p o s c ![zero, v 3, zero] m ∧
                        NKR_DigestCuts.afterCarry m = sums ∧
                          NKR_DigestWrapperView.NativeCut p o s p o s out out 1 ∧
                            NKR_DigestCuts.WrapperCut p o s p o s out out 1 ∧
                              NKR_DigestPrefix.run p o s = ok (c, sums) ∧
                                NKR_DigestPrefix.Frame c sums ∧
                                  NKR_DigestComplete.reference p o s = ok out ∧
                                    NKR_DigestWrapper.reference p o s = ok out ∧
                                      NKR_DigestWrapper.cohort p o s = ok out ∧
                                        (∀ (j : Fin 2), Canon (out j)) ∧
                                          FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s =
                                              ok old ∧
                                            FIw_ArrayValue.canonical old
```

## TX1:250

Focused receipt: `NKR_L168`; exit `0`. Exact stdout SHA256 `7742b4263c3c27b30c332fffe4c33485ddadafba2c88862ce073c273cc01bbd5`.

```lean
theorem AspisR1.NKR_DigestComposed.source : ∀ (p : Public) (o : Openings) (s : Selectors),
  NKR_DigestChildren.Domain p →
    FIw_ArrayValue.canonical o.z →
      FIw_ArrayValue.canonical s.high →
        FIw_ArrayValue.canonical s.low →
          ∃ c sums out old v m,
            NKR_DigestChildren.Clauses p o s c ∧
              NKR_DigestChildren.Canonical c ∧
                NKR_DigestInvocation.PrefixArithmetic c v ∧
                  NKR_DigestPrefixStep.Trace p o s c (List.finRange 4) ![zero, zero, zero] ![zero, v 3, zero] ∧
                    NKR_DigestInvocation.MiddleArithmetic c ![zero, v 3, zero] m ∧
                      NKR_DigestCuts.MiddleNative p o s c ![zero, v 3, zero] m ∧
                        NKR_DigestCuts.afterCarry m = sums ∧
                          NKR_DigestWrapperView.NativeCut p o s p o s out out 1 ∧
                            NKR_DigestCuts.WrapperCut p o s p o s out out 1 ∧
                              NKR_DigestPrefix.run p o s = ok (c, sums) ∧
                                NKR_DigestPrefix.Frame c sums ∧
                                  NKR_DigestComplete.reference p o s = ok out ∧
                                    NKR_DigestWrapper.reference p o s = ok out ∧
                                      NKR_DigestWrapper.cohort p o s = ok out ∧
                                        (∀ (j : Fin 2), Canon (out j)) ∧
                                          FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s =
                                              ok old ∧
                                            FIw_ArrayValue.canonical old
```

## TX1:220

Focused receipt: `NKR_L175`; exit `0`. Exact stdout SHA256 `362c90757286e583bba625e3f9409508ef321a4bb8b12acedae43edf1c1efbbb`.

```lean
theorem AspisR1.NKR_SumFinishComposed.source : ∀ (scratch : NKR_SumFinishInvocation.Scratch)
  (s : NKR_SumFinishInvocation.Selectors) (terms : NKR_SumFinishInvocation.Patterns),
  FIw_ArrayValue.canonical scratch →
    FIw_ArrayValue.canonical s.high →
      FIw_ArrayValue.canonical s.low →
        FIw_ArrayValue.canonical terms →
          ∃ dot coefficients finished,
            BatchTrace (NKR_SumFinishInvocation.tagValues s) (NKR_SumFinishInvocation.weightValues scratch)
                (NKR_SumFinishInvocation.lowValues s) NKR_SumFinishFold.order
                (NKR_SumFinishInvocation.zero4, NKR_SumFinishInvocation.zero4) dot ∧
              PatternTrace (NJB_ArrayCarrier.cell scratch) (NJB_ArrayCarrier.cell s.low) (List.finRange 43)
                  NKR_SumFinishInvocation.zero26 coefficients ∧
                NKR_SumFinishInvocation.reference scratch s terms =
                    ok (NJB_ArrayCarrier.array finished, NJB_ArrayCarrier.array dot.2) ∧
                  FIw_ArrayValue.canonical (NJB_ArrayCarrier.array finished) ∧
                    FIw_ArrayValue.canonical (NJB_ArrayCarrier.array dot.2) ∧
                      (∀ (g : Fin 4),
                          FIv_NativeValue.decode (finished g) = NKR_SumFinishCohort.values scratch s terms g) ∧
                        ∀ (g : Fin 4), FIv_NativeValue.decode (dot.2 g) = NKR_SumFinishCohort.baseWeights scratch s g
```

## TX1:218

Focused receipt: `NKR_L179`; exit `0`. Exact stdout SHA256 `b217c9cb311c45d4aa73d05c90b4b20cdc14de89654ffbf2397d051b22a5d8e1`.

```lean
theorem AspisR1.NKR_SumCopyRoot.source : ∀ (lookup : Lookups),
  NKR_SumCopyAssociation.Keys →
    ∀ (domain : NKR_SumTagPermutation.Domain),
      NKR_SumTagPermutation.Cut →
        NKR_SumTagAssociation.Cut domain →
          ∀ (s : Selectors) (openings : Std.Array NQ 16#usize) (helper lambda chi : NQ) (append : U64)
            (variant : PoolV1PairForestCompiledVariantV1),
            FIw_ArrayValue.canonical openings →
              Canon helper →
                Canon lambda →
                  Canon chi →
                    FIw_ArrayValue.canonical s.high →
                      FIw_ArrayValue.canonical s.low →
                        NKR_SumCopyInvocation.reference lookup s openings helper lambda chi append variant =
                          evaluate_with_selectors openings helper s lambda chi append variant
```

