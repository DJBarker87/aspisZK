# Fresh formatter classification

The historical audit lists 85 nonstandard names. Fresh checked-kernel inventory RPz8_667 classifies **84 as axioms and one as a definition**. The latter is `Aeneas.Std.core.fmt.Formatter := Unit`; it is not an axiom. The pinned coherent library object is SHA256 `63b8efa3940faa81bb26f1b6ea140b2d6b81c1f1155b3fafa0544f6e1e82b9fc` (237376 bytes), resolved exactly as RPz8_Formatter-library-pin.json records. It was already in the retained trusted base; no object or source was replaced.

All 180 named formatter implementation records remain unreachable. All 84 actual formatter axioms are also unreachable. The pure Formatter type definition is reachable. RPz8_666 records exact proof paths and uncached axiom inventories; both roots have exactly propext, Classical.choice and Quot.sound. This matches their raw #print axioms results. The full per-name classification is RPz8_formatter-axiom-reachability.json.

No historical raw audit output is edited. The earlier label “85 nonstandard axioms” is corrected here to “85 historical nonstandard names”. This is an audit classification correction, not a discharged premise or a library/model repair. The all-declaration standard-only gate remains false because the 84 native formatter axioms still exist.

## AspisR1.Rc10_Top.deployed

Proof dependency path (the final edge is a type reference):

`AspisR1.Rc10_Top.deployed` → `AspisR1.FIs_Top.deployed` → `AspisR1.FIs_Headline.deployed` → `AspisR1.FIo_Install.finishOps` → `AspisR1.FIo_Install.pair` → `FIo_Native.weights.Weights.pair` → `FIo_Native.weights.Weights.pair_loop11` → `FIo_Native.weights.Weights.pair_loop11.body` → `FIo_Native.weights.Weights.pair_loop11_loop0` → `FIo_Native.weights.Weights.pair_loop11_loop0.body` → `FIo_Native.weights.Weights.raw` → `FIo_Native.aspis_core.r0.Error.Insts.CoreFmtDebug` → `FIo_Native.aspis_core.r0.Error.Insts.CoreFmtDebug.fmt` → `Aeneas.Std.core.fmt.Formatter`

Exact import path:

`RPz8_Rc10_Top` → `RPz8_FIo_Nonvacuity` → `RPz7_FIo_Install` → `RPz7_FIo_NativeFuns` → `Aeneas` → `Aeneas.Std` → `Aeneas.Std.Core` → `Aeneas.Std.Core.Fmt`

## AspisR1.ARX_Root.deployed

Proof dependency path (the final edge is a type reference):

`AspisR1.ARX_Root.deployed` → `AspisR1.ARW_Observations.observations` → `AspisR1.FIo_Install.finishOps` → `AspisR1.FIo_Install.pair` → `FIo_Native.weights.Weights.pair` → `FIo_Native.weights.Weights.pair_loop11` → `FIo_Native.weights.Weights.pair_loop11.body` → `FIo_Native.weights.Weights.pair_loop11_loop0` → `FIo_Native.weights.Weights.pair_loop11_loop0.body` → `FIo_Native.weights.Weights.raw` → `FIo_Native.aspis_core.r0.Error.Insts.CoreFmtDebug` → `FIo_Native.aspis_core.r0.Error.Insts.CoreFmtDebug.fmt` → `Aeneas.Std.core.fmt.Formatter`

Exact import path:

`RPz8_ARX_Root` → `RPz8_FIo_Nonvacuity` → `RPz7_FIo_Install` → `RPz7_FIo_NativeFuns` → `Aeneas` → `Aeneas.Std` → `Aeneas.Std.Core` → `Aeneas.Std.Core.Fmt`
