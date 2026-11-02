# NEL caller oracles

No multiplication stub was added or used. No multiplication was proved in Kani;
LPh_STUBS.md remains unchanged. SHA values and RuntimePersistence remain approved
trust, and no syscall was unfolded or newly modeled here.

These are local caller oracles, not copy replacements or new field arithmetic.

| Oracle | Domain and interpretation | Model/bridge evidence |
|---|---|---|
| common getter | Actual immutable common field of this actual statement; wrong harness-owned place fails | NED_ReconstructCarriers.common_argument; NEL_GETTER_IDENTITY.json; K006/007 |
| common canonical checks | Every raw typed Digest; actual anchor/nullifier, ordered local log, arbitrary Bool | NED_PaymentCohorts.canonical_result; NEL_CommonOracle; K032/033/060 |
| payment common/canonical checks | Actual same public parameter and immutable fields; every full valid common Result and arbitrary Bool | Closed common/projection bridges; NEL_PaymentOracle and PaymentFieldCarriers; K038/044, K042/043, K058/059 |
| first byte/output lane | Same full raw Digest, arbitrary fixed32/Bool/u8 replies and local log | K002/003, K030/031, strengthened raw controls K058/059; complete child instances remain OPEN |
| late snapshot | Same typed receiver and [32,832) window/prestate, full arbitrary Result, one arbitrary mutation cell | K050/051; NEL_LateDomains; not a complete arbitrary whole-window mutation certificate |
| late afterstate | Actual candidate-afterstate place; full arbitrary Result<[u8;688],Error> | K052/053; actual encoder/refinement instance remains OPEN |
| digest serialization step | Actual raw M31; arbitrary fixed4 reply, local argument log | K012/013; unchanged closed serializer; NEL_DigestLoopFrame is the emitted/value association only |

Every native copy-dependent gate has the exact pinned KMX patch applied. The
actual KMX indexed value operation is checked one iteration at a time; there is
no lane-written copy stub. K058/059 include a matched actual byte corruption.
