# Checkpoint bytes handoff

Closed here:
- CheckpointBytesBody.body_byte_c5: all 1736 bounded extracted source selector
  bytes equal C5, from explicit physical source fields and scalar canonicality.
- Source selector materialization and whole-body checksum equality;
  CheckpointBytesBodyDecodeJoin.decode_checkpoint gives the exact reference
  decoder result, including duplicate-query rejection.
- Production Reader.k width (16), plus K/E output, all canonical scalar
  roundtrips and noncanonical-limb rejection: four unstubbed per-section Kani
  gates with current source pins. Generic bounded raw width/cursor is checked
  separately in Lean; Kani evidence is not relabelled a kernel source theorem.
- Success-conditioned allocation facts: successful resumeWithOps derives
  actual filled success and its dependency on returned weights; successful
  content overwrite determines reservation and contents without availability.

Stopped/unclosed:
- An unqualified checkpoint decode(encode s)=s over merely field-canonical C5
  states is false for duplicate queries. The explicit all-zero state is in
  CheckpointBytesRoundtripBoundary. Use the exact if-injective result; reached
  sampler uniqueness is already derived by accepted_inputs.
- No kernel equality yet identifies extracted arbitrary-byte decode_k_spec /
  decode_e_spec with C5, including Result rejection, and source/reference
  Prepared/Accumulator live in distinct namespaces.
- ResumeOps in the emitted resume body remains parameterized. A generic
  success inversion is not a proof of the actual reader, section helpers,
  heap::filled/resize/Box implementation. No extra operation-adoption premise
  has been hidden in caller binding or state provenance.

Exact next deliverable: a concrete source ResumeOps implementation instance
and its per-operation byte/decoder/content refinement. Consume it with
OraclePortCkptAbiSourceFields.successful_fields, then adopt the checkpoint
stage at OraclePortCkptAbi5Stage.reached_stage through strictStage. Retain
only the intended S2S10CallerBinding and S1S7S8StateProvenance interfaces as
remaining external premises; do not put the desired source observation
equality inside either. Preserve six ordered digest reads through
OraclePortCkptAbi5Decision.decision_observation and dV_frozen2.

No checkpoint ConeJoin/AcceptedRunJoin or deployed security result is claimed.
No shipped source changed; no ELF rebuild, full manifest replay or
whole-function Kani harness ran. Frozen ELF identity evidence is inherited,
not newly measured. New local objects are private, and host gates used the
owned codex-cx-ckpt-bytes2-20261022 offload with the required capped scopes.

Recheck: python3 -B tools/ckpt-bytes2-20261022/audit.py
