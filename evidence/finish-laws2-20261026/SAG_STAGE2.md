# Coherent dot arithmetic and actual reads

SAG_DotTrace, SAG_DotIndexed, SAG_DotReader and SAG_DotAdapter are read-only
S5 candidate reuse with new module/namespace prefixes and import-name changes.
The symbolic productSum induction and same-execution ordered read trace are
retained. Original source paths and hashes are in SAG_reuse.json.

New SAG_DotDecode proves agreement with the actual CheckpointBytes5Output
ofK/ofE on arbitrary raw operands. SAG_DotWeights derives weight-reader meaning
from the actual accumulator definition, with no canonicality premise.
SAG_DotLaw.from_source leaves only sourceDot installation, 64-length and actual
message-reader meanings. SAG_FieldRead reuses F3P_ClaimField's actual record
parser semantics; SAG_EncodedField derives each decoded field from the encoded
message. SAG_FinalPayload derives the exact model final-message encoding from
the SAME aligned transcript/matching-data read, at physical offset8007/2048.

SAG_CommonTail/SAG_ViewTail/SAG_ViewRun recover message slices from the SAME
successful TX2 continuation. SAG_ViewPins checks the actual installed source
constants. Previous Tx2I_Cuts.tail_reached discards these range observations;
no equality with the earlier existential tx2.v2 is silently assumed. Connecting
the enhanced cuts to the actual top remains necessary.

SAG_Freedom.evaluator_not_forced is a checked interface countermodel: an
arbitrary FinishOps evaluator may return encode(poly(alpha)+1), and release
preserves it. This disproves deriving evaluator meaning from release alone,
not a statement about the shipped evaluator. SAG_FinishEquivalent proves
old/new finish-continuation equivalence; only the duplicate quarter family
has been removed so far. No additional ledger credit for these local facts.

39/100 Lean invocations: 31 passes, 8 failed elaborations excluded;0/20 Kani.
All current new modules have successful exact source snapshots and standard
axiom audits. No timeouts/memory kills, cap increases, package replay or new
infrastructure. Reservation scans13 and27 saw other scopes vanish; each waited
30s and retried once, successfully. Exact per-target metrics in raw receipts.
