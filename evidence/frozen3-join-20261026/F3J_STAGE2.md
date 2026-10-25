# Stage 2 — exact semantic digest steps

F3J_InitialLog.initial proves the four-call initialization/row0 log equals
initPair::callLog on the same source call witnesses and reached-call ROM backend.
F3J_SemanticLog.payload and F3J_SemanticValue.payload identify each positive
semantic row's full issued log and challenge/state, without requiring oracle
agreement on unqueried inputs. F3J_PositiveTrace.exact_trace composes these
in chronological order and carries the exact same source successor state.
F3J_SourceBlock.sample and F3J_ValidatedLog.semantic identify the actual installed
source Code observations with those callLog lists. F3J_SourceBlockValue.returned
supplies the actual block return. No independent accepting execution is selected.

These are local refinement lemmas, not a complete33-row or native-pair join.
Remaining: bind them to the constructed proof's actual protocol transcript,
circle rows25/26, opening reseed and rows27..32 including the query decode,
Prepared/accumulator/body and batch/native caller composition. No release
premise removed, no new named trust hypothesis. Every accepted theorem audited
with only standard axioms. Budget26/100 actual Lean,0/0 Kani. No timeouts/OOM.
