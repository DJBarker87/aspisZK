# Native map for pair and finish

Target not yet established. This is the forward (y)(3)/(aq)(5) map, not an inverse raw-log obligation. All inherited artifacts are read-only; hashes are pinned by NJF_INPUT_PINS.json. P6/D188 option-A semantic transport is reclassified, never removed.

| Parent cut | Oracle replies / mutation | Asserted modifies / arguments | Source invocation segment | Coverage assessment |
|---|---|---|---|---|
| NIT cutInitial (NIG initial_stage) | powers4 twice, canonical full arrays | zero7, exact two alpha operands and complete powers replies | NIW_AlignPairPhase.run powers0/powers1 | Existing windows; no allocation result in this cut |
| NIQ/NIG GuardLog allocation/guard | fill success/Allocation; guard Bool | n64/zero fill, owner/folds, same shared flag, prefix/count | NIW_AlignAllocatorPhase, initial regular entry | Regular oracle below is narrow; do not reuse its downstream state claim |
| NIT cutPairEdges | regular_post selected Parts, partial4 | Exact w/alpha/message/scratch/parts and selected ap0/ap1, common and high args | regular -> common16 -> partial -> high | TOO NARROW: regular scratch unchanged; Parts only 2/5/6 plus 1/3 unshared. No returning Err/abort result. Replacement required |
| NIT cutSameGuard | arbitrary regular/partial/high Rust Result<(),Error> | First error, exact finite entered prefix and return tag | NIW_AlignRegularPhase / AfterPhase / PartialPhase | Control only; no mutable footprint. Shared success covered only in control |
| NIW AlignBoundary K002/K004 | full regular Vec and Parts; common16; partial4; high full Parts | Vec owned replacement, selected all-limb Parts and common/high forwarding | regular/shared mutable handoffs | Full value havoc, but Vec replacement is broader/different ABI from actual borrowed slice; lacks full exact argument record. Replace with slice cut; do not infer data from pointer equality |
| NIT cutCommon | one opaque QM31 product | exact two factor cells; one common[j] write, frame others | NIW_AlignCommonCollect/TraceLog/PostLog | One iteration + Lean induction; multiplication discharged in Lean |
| NIT cutLow | E product, quarter-square, scaled E | exact PERM operands, chronological calls; one low[s] write | NIW_AlignLowCollect/TraceLog/PostLog | One iteration + Lean induction; no Kani multiplication |
| NIT TailCuts K003/K004 | grouped E, libra4 | same by-value extra, low/frame and group parts0 write | NIW_AlignGroupPhase/TailPhase | Existing arguments/value windows; loop segments separate |
| NIT cutLibraLog | field E, product E, add E | exact field message/index, old parts4; only parts4 write | NIW_AlignLibraCollect/TraceLog/PostLog | One iteration + Lean induction, field abort prefixes retained |
| NIT cutFinal | product E, add E | exact powers[kind], parts[kind], sum and order; sum only | NIW_AlignFinalCollect/TraceLog/PostLog | One iteration + Lean induction |
| NIT cutNewPort | Option<Box<Weights>>, all errors | variant/semanticAlpha/z, Box move/address only | NIW_AlignFinishComposed NEW | Does not claim payload identity |
| NIW AlignOwner K006/K008 factors + K009/K010 rest | actual complete owned arbitrary Weights, eight errors | full raw field windows on same pre-call owned value, move unchanged | NEW returning payload into pair | Full payload law supplies missing NewPort payload; K005/K007 timeout shapes excluded |
| NIT cutPairPort | canonical Result<E,Error> | exact owner/alpha/message/kappa, complete encoded result and owner frame | NIW_AlignFinishPort | Retained reviewed PairPort cut, no assumed child success |
| NIT cutFinishLog | two round Results; NEW; pair Result; dot Result | exact chronological prefix, round claim chaining, all reached args, parent Result | NIW_AlignFinishComposed / ComposedRoot.source | Read-only parent data; nested NEW payload uses independent window law. Complete source abort prefixes supplied by NIW, never assume a successful suffix |

Shared regular success has no complete prior native slice cut (NIW RegularNativeProject returns none). The new NJF cut must cover it, including common/partial/high entries and high Err writes. Native abort-only outer fail/div semantics are treated by ruling (an); Rust Err branches remain explicit constructors under (ak). No root takes RegularProjection, PairWitness, FinishProjection, child Result equations or endpoint equality as a premise.
