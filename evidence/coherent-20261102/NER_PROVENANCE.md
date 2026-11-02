# NER provenance, stage A

The recovered Lean sources do **not** differ in `stage2_owned`. The exact
function diff is empty (`NER_STAGE2_DIFF.txt`). The full file diff is
`NER_Adapter_sources.diff`: the historical source adds only a trailing
`#print axioms AdapterRw.Ops`. A differing frozen implementation is not
established by these sources. Generated matcher identities differ by build.

| Item | SHA-256 | Location |
|---|---|---|
| Historical Adapter source | e09bfc695970e18f47abacb6dcb6d43820c100dfaf68e54f6923dd84c69cc46d | host codex-cx-sound-int2-20261025/source-inputs/AdapterRwModel.lean; repository evidence/port30join-20261025/sources/d346dc7cb7-AdapterRwModel.lean.txt and evidence/native-tx2a-20261027/NBC_COHORT_AdapterRwModel.lean.txt |
| Headline Adapter source | c6aa4d351e409cc56ee59b64c573590fddca8831f7abba0634ac35ef80bcf497 | repository docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean; host codex-cx-replay-dry-20261026/RPz4_sources/AdapterRwModel.lean |
| Historical Adapter object | 599c5663925f3060d2f07c37e0393fdd581a1ebfdd2adecee67d3214bef52683 | host codex-cx-sound-int2-20261025/objects/AdapterRwModel.olean |
| Headline/NDR Adapter object | 010bcafdfc369d2df13217a13cdc16cdd0369d499bf4e6676feccac084a69c80 | host codex-cx-reconcile-cache-20261028/objects/AdapterRwModel.olean; byte-identical to codex-cx-replay-dry-20261026/RPz4_objects/AdapterRwModel.olean |
| JGx source | c9558c6b0574d236d5c50052dfe1d6aca0c84f837a5a106067c4dc137018cb2c | repository lean/JGx_SdkAfterValidationEq.lean and evidence/fixture-tx2s-20261027/JGx_TX2_050/sources/JGx_SdkAfterValidationEq.lean; host sound-int2 cache |
| JGx object | 9784b7f37ce269a3a82fa3a1259b21d04a23ec1b79e1370995c414757cfe81fa | host sound-int2 root and NDR objects (byte-identical) |

Host paths in this table are under `/home/dombarker/project-offloads/`.
The NDR manifest pins the headline Adapter object, not the historical one.
`RPx_Deployed.deployed` uses that headline cohort. Its object pin is recorded
in NER_NDR_selected_pins.json.

The JGx receipt `JGx_TX2_050` records compilation on source revision
5c4d72a3d707dfc71f3e6d6eb283df07fce38d78 (dirty source), exit 0, 2.766104 s,
4,411,192 KiB peak RSS, zero swaps, the standard three printed axioms, and
Lean binary e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550.
Its direct import pin is JGx_SdkContinuation a69a4ecf…; the Adapter input is
not directly pinned by that receipt. The recovered original cache plus
JHd_LIBRARY_PINS and the historical selected-import ledger identify the
599c5663… build in that cohort. The latter ledger locates its earlier copy at
`/tmp/s126-current-caller-20261021-objects/AdapterRwModel.olean`.
This identifies the paired historical build, not a reconstruction of its
original compiler invocation.

Headline Adapter receipt `RPz4_1070` pins source c6aa4d35…, revision
81a885b535541211ef389ed3dea1c04aed999743, exit 0, 3.915094 s,
2,750,952 KiB RSS, zero swaps, standard three printed axioms; its imports
include AdapterRwTypes dc1e32a2… . Both historical receipts are retained here.

NER_R003 reads the two original serialized tables directly: historical stage2
uses and declares match_3/match_1; headline stage2 uses and declares
match_2/match_1. Its receipt records exact target, revision, limits, exit,
wall time, RSS and swaps. It is a table inspection, so #print axioms is N/A.
The cause of the generated-name difference is not yet established. No source,
protocol parameter, theorem contract or frozen proved module was edited.

A stronger independent source pin was recovered after stage A:
NER_historical_Adapter_source_pin.json (extracted from
XSf_DEPENDENCY_CLOSURE.json) links object 599c5663… to source e09bfc69…
at revision d346dc7cb7232f12c4ff930d1e2db320bdc101d9, path
`docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/AdapterRwModel.lean`.
