# Append proof plan — not a proved obligation

The exact consumer is SpendRelation.AppendBinding. It needs the output-pair
shape, root = pathPrefix pair 20, and the one carry frontier cell when carry<20.
It does not assert preservation or correctness of every frontier cell.

Reuse the exact successful late_append read of CopyRecords.append_root to bind
the returned next.root to appCurR at20, then appCur_lift and appCur_eq. This avoids
re-evaluating the full reconstruction routine or asserting a stronger tree law.

For the remaining carry cell, prove a symbolic induction on20-carry_level for
OwnedTree.append_one_loop, preserving frontier entries at or above carry_level.
Its full-Result body reads frontier[level], hashes frontier[level] on the left
and carry on the right, clears exactly that frontier cell to empty[level], and
advances level. Stop at the first zero bit or20. Parent source law is already
available from LaneField31; no concrete Poseidon normalization is appropriate.

The bit transport is the same shift64_spec calculation as the checked
PV_Src_Forest_AppendArguments.append_bit. Relate the stopping level to
R0P.digestTrailingOnes20 on the same raw next_pair_index via publicCorr.next.
When carry<20, successful append_one updates that exact cell with the carry
before reconstructing the root. Recover the returned frontier from this source
path. For carry=20 the conditional frontier clause is vacuous.

Prove the constructor/returned-state bookkeeping separately; successful
from_parts returns the passed cursor/root/frontier and roots without changing
those fields. Preserve every Result and error layer. Existing fixture index0
lemmas are patterns only and do not establish this universal case.

Do not promote this plan to a result, compile its obligations, or proceed to
recipient/sentinel or V038/V045 until the input obligation is complete.
