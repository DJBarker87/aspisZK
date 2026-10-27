# Joint fixture21 progress

S2 OPEN; deployed target not yet established. Actual branch is
codex/cx-joint-fixture21-20261027 (prompt's initial suffix was 20261026).
Only JGl-prefixed modules and this receipt directory are changed.

## Stage 1: internal pair and real native success

FJh_InternalPairValue.value and FJh_InternalOnRun.value require actual success;
they are value refinements, not forward success constructors. Their operands
are the exact state/local-selector pair required by JGb, with no mismatch.
JGl_InternalMaps constructs the original ROWS selector/constant maps.
JGl_InternalPairTotal.source composes FJh_M31DotSevenExact.source_success
and JGj_InternalRoundTotal.source, then applies FJh_InternalPairValue.value
to that very return. No component is reproved or guard weakened.

JGl_RealFixture.inhabited selects JGb_Fixture.inhabited's SAME witnesses and
constructs all three packed calls. Its formerly conditional continuation is
now unconditional: actual projected evaluator suffix, composition, and public
native terminal success/canonicality/value formula. This does NOT yet identify
the terminal with JGd_NumericData.neededTerminal and is not accepted1/accepted2.
No vacuity counterexample has been found.

Validation: attempts 001/002/004 pass; 003 failed for a missing JGb_Fixture
import, fixed in 004. Per-attempt receipts pin target, source revision/hash,
dependencies, exit, wall, peak RSS, swap, command and axioms. All accepted
new theorems use only propext/Classical.choice/Quot.sound. Host scopes use
6G high,8G max,swap0,Tasks64,-M7000,-j1; one scope at a time. Existing coherent
SInt2 objects reused, d18 v5 before aspis-joint. No package replay or ELF build.
No shipped source changed, so inherited ELF pins are not freshly reproduced.
Top ARX_Root.deployed remains unchanged: no top-premise removal claimed.
