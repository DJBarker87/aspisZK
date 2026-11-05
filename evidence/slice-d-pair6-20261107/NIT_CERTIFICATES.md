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

## New parent-tail gap cut

`NIT_TailCuts.cut`: reviewed transcription of `evidence/slice-d-pair6-20261107/NIT_tail.rs.txt`, SHA-256 `764bd72c34a30ea68fe30242269d9979d5469026a96d69d161005216aab049a7`. Corrected positive K003 SUCCESSFUL (624 checks, one unreachable outside-S2 panic); identical-name/configuration control K004 FAILED the grouped reply/frame and copied-extra assertions. K001/K002 are EXCLUDED candidate evidence (borrowed/owned argument mismatch, NIT-F1). Native shape checker NIT_NATIVE_SHAPE.json accepts the exact by-value interface and rejects five mutations.

Observed: SAME grouped w/f/low arguments; only parts0 takes grouped reply; SAME factored ap0/ap1 and copied extra words; exact ordered two-call log; opaque libra array forwarded; isolated final returned Result is Ok(sum). These are the two frozen source fragments around the independently composed loops, not a whole-tail or whole-pair success statement. Composition-trust option A reclassification; inventory unchanged. Both runs use the exact KMX patch pinned in NIT_KMX.json and pass frozen graph/offline/unchanged-lock checks with deployed feature lists. No multiplication, function contract, stub_verified, Option<fn> or writable-static credit.

Final review status: all eleven cut entries above are reviewed local transcriptions; projection/interface checks and standard-only raw axioms are recorded. Restricted pointer views are explicit in NIT_RefInterpretation. NIT_EdgeInstantiation, NewPortInstantiation, PortInstantiation, NativeGuardJoin/GuardFrontJoin and FinishArguments prove local same-input/domain/control associations. None is a native whole-parent execution certificate. Exact open joins are NIT_OPEN_EDGE.md; zero inventory rows promoted. Supporting proof closure was audited once in the combined158-root raw walk and coherent13788-module scan. No trust item added or removed.
