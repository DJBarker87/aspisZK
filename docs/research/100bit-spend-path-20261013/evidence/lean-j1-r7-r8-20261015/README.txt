Focused local Lean checks for J1.R7/R8 proposals.

Nine new targets compiled with Lean 4.32.0 through the pinned AspisFormal
lake environment. The checkout's default elan version is recorded separately
and was not used for these checks. Every final receipt is exit 0, zero swaps,
with no memory kill. All 53 printed axiom reports use only subsets of propext,
Classical.choice and Quot.sound. Failed development attempts are retained;
their sorryAx diagnostic reports are NOT green audit evidence.

Each target used lake env lean, -M6000, sequential scheduling and an aggregate
process-group RSS monitor stopping above 7 GiB. No full manifest, dependency
rebuild or build-host Lean process ran. No imported theorem was replaced by
an axiom. The raw model's final check adds missing axiom-print evidence;
the semantic codec final check pins its corrected final header bytes.

Final-targets.json pins exact target sources/objects, successful receipts,
wall time, process peak RSS, sampled aggregate RSS, swaps and axiom output.
Sources and target objects are included. Direct-import-pins.json pins the
final dependency state. Definitions in the two final header/audit-only
refreshes are unchanged from their dependent targets' original checks.

Cache reuse: most objects come from the retained local J1 cache for 95bf664bc,
plus tracked e4a5808dd evidence archives listed in integrated-cache-pins.
64 missing objects (Gen/BS and 62 literal-closure dependencies) were copied
read-only from retained build-host caches. 63 adjacent/current source copies
matched repository bytes; SamplerCirclePolicy's adjacent source was not found.
All copied object hashes are pinned. These source/object inventories are NOT
new historical source-to-object build attestations. Earlier cache provenance
is recorded in the 95bf664bc J1 coordinator evidence. No cold rebuild is implied.

The new theorems are conditional model results. SourceSerializerRefines,
actual Rust parser/challenge execution, D1/D2/D3, raw-byte injection/collision
mass, efficient extraction and SourceCountObligation remain open as described
in design/J1-R7-R8-STATUS-20261015.txt. Budget equalities are arithmetic, not
source execution bounds. SBF source/artifact correspondence is not checked here.
