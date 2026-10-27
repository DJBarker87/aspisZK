# Mapper boundary and variant transcription

The actual Lean extraction's exact interface is
BuilderForestAdmissionPort.Records.call (BuilderForestAdmissionPort.lean:4362).
The `records` declaration at 4372 is exactly `sourceRecords.call`. It has no
implementation body to unfold. No concrete deployed Records instance is
published by RunJoin10; its installed_admission theorem takes the equality.

PV_Src_MapperBody is explicitly a new transcription. Its direction-array call
is the actual extracted native compiler closure; all other witness/public fields
are stated directly, using the same source path selection and the source root
helper. The accepted call_eq proof (40067) compares this new body with the extracted
owned reference for arbitrary inputs, recipient variants, selected-first/second,
snapshots, assets, and every complete Result of the actual root helper. It does
not abstract the helper to a table and does not use a Kani stub.

PV_Src_MapperWords supplies candidate dictionary/word admission after that
comparison (40069). It retains PV_Src_RecordReference.Checked on the selected input.
The source-to-deployed association is NOT inferred from the transcription or
from naming it `call`. To close the deployed `words` row still requires a
source-derived value for the actual opaque Records field and its exact equality
with this candidate, plus the same installed checked canonical selection.
No new P6 success is credited to the srcid5/srcid6 mapper timeouts.

Stage 2 receipts: 40065/40066/40068 rejected local proof drafts; 40067 and 40069 accepted. No failed draft is an installed source link. No mapper Kani run was used.
