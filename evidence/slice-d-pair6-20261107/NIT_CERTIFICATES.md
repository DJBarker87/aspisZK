# NIT cut certificates — reviewed transcription inventory

TX2:129/TX2:115 OPEN. These items reclassify native contract semantic transport under the existing P6/D188 composition-trust option A; no trust item is added or removed. They are not endpoint proofs. NIT_INPUT_PINS.json pins the inputs once. NIT_Cuts.lean docstrings quote the native assertions verbatim.

All-limb assertions are transcribed by structural equality of the four/eight raw fields; frozen WideExact::to_limbs returns those raw fields unchanged. Finite arrays retain their model size. Nat address tokens preserve only identity; Ref carries a chosen decoded payload and does not identify arbitrary equal-address payloads. No such identification is used as a theorem. This ABI/content association must be discharged at composition, not silently inferred from address equality.

| Cut | Native assertion range in pinned patch | Asserted frame |
|---|---|---|
| `cutInitial` | 181–196 | zero parts; two powers replies forwarded |
| `cutCommon` | 24–37 | one cell changed to opaque reply |
| `cutLow` | 46–63 | one cell changed to scaled reply |
| `cutFinal` | 71–84 | sum changed to add reply |
| `cutLibraLog` | 92–105 | only parts4 changed |
| `cutSameGuard` | 161–179 | first error and exact finite event prefix |
| `cutPairEdges` | 199–219 | arguments only; no payload post-state assertion |
| `cutNewPort` | 225–236 | Box owner/move-presence only; no payload equality assertion |
| `cutPairPort` | 238–250 | full encoded Result and same owner |
| `cutFinishLog` | 253–292 | full returning Result, ordered events, conditional arguments |

Patch: `evidence/slice-d-pair4-20261107/NIG_stages.patch`, SHA-256 `907f959aa06466d25e615fb135d898b15a90e7eac7515bdaf733ba1a3dd46289`. NIG/NHX source variants and receipts are inherited and are not rerun here; no new Kani pass claimed. All canonical assumptions come from native anye generation, not from opaque success. Common raw QM31 words remain unrestricted until caller factors provide canonicality.

Caveat: full native pre-state projection and address/content transport review is ongoing; compilation alone does not certify this table or close a row. No broad heap frame or callee output interpretation has been inserted into any cut.

Pre-state review correction (stage3): native anye assumptions on reached Prepared alpha/kappa/claim, accumulator rhs and returning field replies are now explicit; NewPort now states the initial reply's known owner and S2 payload variant. The earlier compiled cut versions omitted those assumptions and have no native credit. NIT_PROJECTION.json checks the exact field-read/forward sets of new_cut/pair_cut/finish_cut and rejects six footprint mutations. The seeded but unused roots/gamma/rho/queries/state are absent from those stages; this is a source-footprint projection, not a new caller precondition.
