# Runtime CPI entry transport — ADDED-PENDING-LEAD, unused

B3 needs a relation from the very Pool `program::invoke` call to the callee's
entrypoint inputs. RuntimeReturnData (ab') relates a nonempty write/read in one
instruction context; it does not itself state that dispatch preserves the
instruction/account inputs. RuntimePersistence covers data across transactions,
not owner/balance/privilege transport. The adopted S2TrustedSdkBorrow boundary
explicitly excludes CPI. A native log of SDK arguments alone does not assert
what the external runtime does with them.

Proposed minimal row RuntimeCpiReadonlyEntry7, NOT ASSUMED OR USED:

Fix an instruction context I and bank state B immediately before the very
Pool invoke call, after any earlier marker System CPI. Let the native caller
submit Instruction { program_id=P, accounts=ms, data=b } and infos. Require
ms has exactly seven pairwise-distinct keys k[0..7), every meta is readonly
and nonsigner, P is distinct from those keys, infos supplies those SAME bank
accounts and the executable program account P, and runtime CPI/ABI admission
succeeds. This invocation dispatches P's entrypoint; a normally returned invoke Ok requires that very entry execution to return Ok. At entry its program_id is P,
its instruction_data is byte-for-byte b, and its seven account inputs, in that
order, denote B's accounts k[i], with the SAME key/owner/data/lamports/
executable/rent_epoch observations and is_signer=false, is_writable=false.
The entry heap is the runtime-admitted heap for those callee records, not a
claim of equal virtual addresses across the two programs. If this readonly
invocation returns Ok, those seven bank accounts' observations are unchanged
by it. The row asserts neither verifier admission nor acceptance, no decoder
success, and no security bound. Return-data contents remain solely (ab').

The native caller still has to derive b=the SAME encoded320-byte request,
P=the selected authenticated verifier, the seven keys/order/flags, all
uniqueness/admission hypotheses, and all callee PacketDomains. None follows
from this proposed row. Marker and custody CPI writable-state laws are not
included: their exact call/modifies/domain certificates remain separate OPEN
obligations.

The lead may identify an already-adopted item that states this exact transport,
or approve this as an ADDED runtime trust row. Until then it is an explicit
B3 boundary finding, never a hidden consequence of P6/D188 or a new axiom.
No theorem in this job takes this proposal as a hypothesis.
