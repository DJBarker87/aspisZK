# Pair installation check

The adopted `AspisR1.ARX_Root.deployed` uses
`FIp_Install.configuration indexError c reservation`.
Its PAIR slot is **fixed**, not a callback of `c`:

```
(FIp_Install.configuration err c r).finish.pair = FIo_Install.pair r
```

`FJr_Installation.pair` proves this identity by definitional equality for every
`C`, `err`, `c`, and reservation `r`. Attempt FJr_001 passed (exit 0,
5.108970578003209 s, peak RSS 5433272 KiB, swap 0); axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`. Exact command, source revision/hash,
dependency fingerprint, scope and limits are retained in FJr_001/receipt.json.

The source chain is FIp.select -> FIo.select -> FIo.finishOps, whose pair field
is FIo.pair. Rc5 and its intervening installers preserve that finish field.
ARX's free binder `c : DrvC_Installation.Configuration FIo_Install.W CoreError`
therefore does not leave Pair unconstrained. In contrast, the terminal remains
`c.boundaries.terminal`; no terminal installation change is made here.

This check establishes installation identity only. It removes no L142 law and
is not a security or non-vacuity result. Continue with the installed Pair value
proof. No existing source, installation or artifact was changed.
