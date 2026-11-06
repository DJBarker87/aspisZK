# NJX root statements and hypothesis inventory

Target not yet established. Candidate roots below are actual successful compiler statements. Each has only SAME typed input/canonicality domains; every child Result, constructor/cache domain, frame and cohort equality is derived in the conclusion. Incoming parent domain discharge remains with the parent row. No success, output, endpoint equality, Run, arbitrary Ops or runtime-outcome Bool is a root hypothesis.

## TX1:224

Receipt: `NJX_L035/receipt.json`. Source `NJX_PatternRoot.lean` SHA256 `2b9c9d71eb56befec6d752c05d0ff7df5d231e11cf0f26e38c85e5338265dedb`.

```lean
theorem AspisR1.NJX_PatternRoot.source : ∀ (lambda : NQ) (o : Std.Array NQ 16#usize),
  Canon lambda →
    FIw_ArrayValue.canonical o →
      ∃ p w out,
        NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun x => FIq_Native.field.QM31.ZERO) lambda =
            ok (NJL_CacheReads.power p, p.next) ∧
          NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun x => FIq_Native.field.QM31.ZERO) lambda
              (NJL_CacheReads.power p) p.next ∧
            (∀ (j : Fin 4),
                NJL_WindowFold.run (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8)
                      FIq_Native.field.QM31.ZERO =
                    ok (w j) ∧
                  NJL_WindowFold.Trace (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8)
                    FIq_Native.field.QM31.ZERO (w j)) ∧
              (NJX_PatternTail.run p (NJX_PatternPacket.atoms o w) (List.finRange 14) fun x =>
                    FIq_Native.field.QM31.ZERO) =
                  ok (cells out) ∧
                NJX_PatternTail.Trace p (NJX_PatternPacket.atoms o w) (List.finRange 14)
                    (fun x => FIq_Native.field.QM31.ZERO) (cells out) ∧
                  FIw_ArrayValue.canonical out ∧
                    FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values o lambda = ok out
```

## TX1:223

Receipt: `NJX_L042/receipt.json`. Source `NJX_PatternForward.lean` SHA256 `2365fd4a5d3d72407f771cae10994836c200e2af5eea1f21bdb4f45251dbe37b`.

```lean
theorem AspisR1.NJX_PatternForward.source : ∀ (lambda : NQ) (o : Std.Array NQ 16#usize),
  Canon lambda →
    FIw_ArrayValue.canonical o →
      ∃ p w out,
        NJL_WindowPowerFrame.run lambda (List.finRange 8) (fun x => FIq_Native.field.QM31.ZERO) lambda =
            ok (NJL_CacheReads.power p, p.next) ∧
          NJL_WindowPowerFrame.Trace lambda (List.finRange 8) (fun x => FIq_Native.field.QM31.ZERO) lambda
              (NJL_CacheReads.power p) p.next ∧
            (∀ (j : Fin 4),
                NJL_WindowFold.run (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8)
                      FIq_Native.field.QM31.ZERO =
                    ok (w j) ∧
                  NJL_WindowFold.Trace (NJL_CacheReads.cache p) o (NJX_PatternPacket.starts j) (List.finRange 8)
                    FIq_Native.field.QM31.ZERO (w j)) ∧
              (NJX_PatternTail.run p (NJX_PatternPacket.atoms o w) (List.finRange 14) fun x =>
                    FIq_Native.field.QM31.ZERO) =
                  ok (NJX_PatternRoot.cells out) ∧
                NJX_PatternTail.Trace p (NJX_PatternPacket.atoms o w) (List.finRange 14)
                    (fun x => FIq_Native.field.QM31.ZERO) (NJX_PatternRoot.cells out) ∧
                  FIw_ArrayValue.canonical out ∧
                    FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values o lambda = ok out ∧
                      Cut o o lambda lambda out out 1
```

## TX1:242

Receipt: `NJX_L052/receipt.json`. Source `NJX_LeftCutRoot.lean` SHA256 `d7524c8cd0932d08ae180a8bbd5baf678b99b5dce2ee2c17745352b65b7afe4b`.

```lean
theorem AspisR1.NJX_LeftCutRoot.source : ∀ (high : NQ) (o : O) (d : D),
  Canon high →
    FIw_ArrayValue.canonical o →
      dc d →
        ∃ p,
          NJX_DigestPacket.reference high (ocells o) (dcells d) = ok p.out ∧
            NJX_LeftRoot.cohort high o d = ok p.out ∧
              NJX_DigestCut.Cut high (ocells o) (dcells d) p.prepared
                (fun i => FIw_ScalarArithmetic.lifted (dcells d i)) p.residual p.packed p.out p.out
                (NJX_DigestCut.log p) 21
```

## TX1:245

Receipt: `NJX_L047/receipt.json`. Source `NJX_CarryRoot.lean` SHA256 `53ec12b54398960a15f468c2e21df1ccd0962a30006385505c3b8a7356196939`.

```lean
theorem AspisR1.NJX_CarryRoot.source : ∀ (carry : ℕ) (high : NQ) (o : O) (d : D),
  Canon high →
    FIw_ArrayValue.canonical o →
      dc d →
        ∃ out,
          reference carry high o d = ok out ∧
            cohort carry high o d = ok out ∧
              (∀ (g : Fin 2), Canon (out g)) ∧
                if carry < 20 then
                  ∃ p,
                    out = p.out ∧
                      NJX_DigestCut.Cut high (ocells o) (dcells d) p.prepared
                        (fun i => FIw_ScalarArithmetic.lifted (dcells d i)) p.residual p.packed p.out out
                        (NJX_DigestCut.log p) 21
                else out = zero
```

## TX1:246

Receipt: `NJX_L053/receipt.json`. Source `NJX_RecipientRoot.lean` SHA256 `ae979cc8b7104a5f8927230028fdbd4cc2530bb7f06374388c6904ae01d7b2f0`.

```lean
theorem AspisR1.NJX_RecipientRoot.source : ∀ (recipient : Option D) (o : O) (high : NQ),
  Canon high →
    FIw_ArrayValue.canonical o →
      (∀ (d : D), recipient = some d → dc d) →
        ∃ out cache,
          reference recipient o high = ok out ∧
            cohort recipient o high = ok out ∧
              (∀ (g : Fin 2), Canon (out g)) ∧
                Cut recipient o high (if recipient.isSome = true then 1 else 0)
                    (if recipient.isSome = true then 2 else 0) high o recipient cache (fun x => cache) out out ∧
                  ∀ (d : D),
                    recipient = some d →
                      ∃ p,
                        out = p.out ∧
                          FIq_Native.field.PreparedQm31Multiplier.new high = ok p.prepared ∧
                            ∀ (g : Fin 2), NJX_RecipientBody.group p.prepared (ocells o) (dcells d) g = ok (out g)
```

## Expanded domain/packet review
`Canon` is four actual M31 word bounds<P (P=2147483647); array canonicality quantifies the actual array's cells. Digest canonicality is each actual8word expected digest<P. No bit-valued opened/occupied restriction is added. `carry : Nat` covers every decoded Rust usize; the guard is computed `<20`. Recipient is the actual data Option<Digest>; only an entered Some requires its digest bounds. No Option<fn> is used.

`NJL_CachedPowers.Packet` and `NJX_DigestPacket.Packet` are existential OUTPUT records. Their constructor, PreparedFor, child Results, canonicality and frames are proved by the root's helper chain. They are not premise bundling. Full printed definitions and cut statements are in NJX_L068/stdout.log. The same four window replies use ONE internally constructed powers/cache packet. Digest/recipient outputs are exact full raw2cell carriers, not merely decoded-value matches or successful fixtures. Canonical injectivity is applied only after BOTH carriers are proved canonical.

The 5 roots require no NIG_FinishInput.Domain, operation dictionary, accepted-execution premise, new runtime trust, physical exporter, inverse raw-log association or XRn stand-in. Native-to-source is the (y)(3)/(aq)(5) forward substitution of actual CLOSED field/pack/constructor Results into reviewed cuts on the SAME decoded arguments. All field operations are pure with empty external effects; mutable frames cover every local cell. Caller/native/ABI/compiler/source-to-ELF interpretation is retained P6/D188 option-A reclassification, never removal. No headline hypothesis is discharged by these local rows.
