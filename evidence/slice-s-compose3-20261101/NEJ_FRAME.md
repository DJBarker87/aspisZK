# Common encoder frame decomposition

The frozen common encoder has ten ordered writes. NEJ_CommonFrame.run_spec
composes their KMX_CopyMeaning.loop value laws for an arbitrary prestate and
arbitrary source bytes. common_bytes identifies exactly the union [0,7) and
[8,148); reserved_frame preserves byte 7 and every byte from 148. window_disjoint
proves the frame between disjoint windows without a zero-prestate hypothesis.
These are byte-model theorems, not native-root refinements.

NEJ_L002: exit 0, 1.4514395410660654 seconds, peak RSS 754712 KiB, swaps 0.
Exact command, source revision, source/dependency/Aeneas hashes and caps are in
NEJ_L002.json, NEJ_L002-pins.json and NEJ_L002/receipt.json. All five printed
axiom lists are [propext, Classical.choice, Quot.sound]. L001 was an excluded
elaboration failure involving a dependent Decidable rewrite; the corrected
source uses simp only. Its sorryAx diagnostic is not accepted evidence.

NEJ_K005 passes the isolated native version-byte write on arbitrary Common,
output prestate and observation index. The original statement is copied exactly
from frozen encode_common into a scratch-only window. It has an explicit
modifies(output) contract. This is not yet the full function's frame: control,
other windows, child reply association, pointer bounds and model join remain.

K001/K002/K003 failed compilation on missing frozen include files; K004 failed
on a generator placeholder collision inside a constant name. All consume budget;
none earns proof credit. K003 was accidentally submitted after a source repair
script failed decoding a binary. Campaign scripts now stop on predecessor
failure (Python check=True). Source repair copies only frozen textual includes,
verifies every existing checked source byte unchanged, and pins the new bytes.
No timeout occurred in these attempts. No shared infrastructure was edited.

NEJ_validate adds checks to the unchanged NDT/NED/NEE chain, requiring explicit
new call-domain theorem bindings and complete native frame before new NEJ credit.
Ten real-certificate/mutation tests pass; missing/wrong certificates remain OPEN.
The NEE modules/validator are imported without reproving or altering them.
