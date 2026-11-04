# Accumulation packet joint-import finding

L038 imports NEV_AccumPacket alongside the selected NFM/Stage2 source forest.
It fails before checking NFP_AccumDomain statements:

    import S1SemanticPhaseV1 failed, environment already contains
    'AspisR1PublicPreparation.verifier.Phase' from AspisR1PublicPreparation.Types

The same legacy path was isolated earlier through LPi_Total/LPf_BaseMultiply
(L012--014). NFP_NatBase replays the SMALL input-only scalar lemmas with a
canonical import and unchanged proof bodies. That repairs scalar node laws;
it does not repair NEV's accumulated-row packet or claim its joint closure.
NEV_MaskCarriers imports NBG_FieldDischarge, through the legacy LPi field
forest; LPi_Total imports the original FIo_NativeFuns. The selected NFM
forest instead uses the canonical retargeted FIo owner. The failed packet is
not imported into NFP's final coherent support module.

The accumulation callee's existing standalone CLOSED source packet is not
headline-composable on this selection. No CLOSED query_values/query_loop row
may be booked until its field/carrier dependency closure is retargeted and
replayed jointly. This is a source-refinement/coherence obligation, not a new
cryptographic assumption or an SDK/runtime trust row. The retained NFA/NFC
axiom audit of standalone NEV roots does not itself prove this joint import.
NFP_AccumDomain.lean.txt is a rejected candidate, not an accepted theorem.

Independent work continues: the original dot incoming window, trace/value,
scalar node and geometry access windows, full owned return frame, source trace
factorization and finite partial-Result loop transport. Prepared/powers/prepare
remain out-of-slice producer boundaries. No NEW/NFB geometry forest is imported.
