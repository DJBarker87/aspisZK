# AspisLib base modules: carrier reach and definition identity

| module | namespace | direct imports | carriers reached transitively | copied definitions (sha256 of original decl text = copy) |
|---|---|---|---|---|
| AspisLib_SourceInputs | AspisR1.AspisLib.R1FinalSoundness | 15 | none | SourceInputs 93398351cb18=93398351cb18 |
| AspisLib_Recorded | AspisR1.AspisLib.RecordedBinaryExperimentBin | 19 | none | dec 32678995ddfa=32678995ddfa; binaryCollision acd491901a6f=acd491901a6f |
| AspisLib_Tag | AspisR1.AspisLib.InitialTagDecision | 24 | RecordedBinaryExperimentBin | erased_transcript_tag 538eb908911f=538eb908911f |
| AspisLib_QueryAccounting | AspisR1.AspisLib.DecoderQueryAccounting | 20 | none | starts_le_queries be98512de640=be98512de640; AdversaryQueries 2787a2afcf73=2787a2afcf73 |
| AspisLib_Guard | AspisR1.AspisLib.OraclePortAdmission | 26 | DecoderQueryAccounting, QueryScanRow31SourcePlacement, R1FinalSoundnessBinPerQuery, R1FinalSoundnessBinPerQueryR18, R1FinalSoundnessBinPerQueryR19, RawChecksAdaptiveFailureNoModelBin, RecordedBinaryExperimentBin | Guard fd845375fa14=fd845375fa14 |
| AspisHonestBudgetBase | AspisHonestBudgetBase | 1 | RecordedBinaryExperimentBin | raw 1e47fe58d8d1=1e47fe58d8d1 |

## Residual carrier paths (through kind-c modules; cut by the whole-closure trim)

- AspisLib_Tag: cut the import line(s) RWireInitialTag -> RecordedBinaryExperimentBin
- AspisLib_Guard: cut the import line(s) DecoderFiniteStartSupport -> DecoderQueryAccounting; R15WriterModel -> R1FinalSoundnessBinPerQueryR18; R16DecisionErasure -> R1FinalSoundnessBinPerQueryR19; RWireInitialTag -> RecordedBinaryExperimentBin
- AspisHonestBudgetBase: cut the import line(s) BinDecoderInitialStarts -> RecordedBinaryExperimentBin

## Revision 2 (original names + import map)

Base modules now declare the seven names under their ORIGINAL fully qualified names (AspisR1.R1FinalSoundness.SourceInputs, AspisR1.RecordedBinaryExperimentBin.dec/binaryCollision/SourceInputs, AspisR1.InitialTagDecision.erased_transcript_tag, AspisR1.DecoderQueryAccounting.starts_le_queries/AdversaryQueries, AspisR1.OraclePortAdmission.Guard); declaration text verbatim. trim_imports.py takes `--map carrier=Base` and replaces the carrier import line by the base module import (IMPORT_MAP.txt). Consequence, tested: a base module and its carrier cannot be in one environment (`import R1FinalSoundness failed, environment already contains AspisR1.R1FinalSoundness.SourceInputs._sizeOf_1`), so under the L187 object set only the bases whose import frontier is carrier-free compile before the trim: AspisLib_SourceInputs, AspisLib_Recorded, AspisLib_QueryAccounting (compiled). AspisLib_Tag and AspisLib_Guard, and every trimmed kind-c module (BinHonestStartFrames included), compile only in an object set built after the trim in dependency order: bases first, then trimmed kind-c modules, with the trimmed objects shadowing the L187 objects on LEAN_PATH. That is X3's whole-closure run.
