# PCB stubs and trust

No field multiplication stub is used by the CLOSED scalar246 or inherited354 packets.
Their native domains contain no field multiplication. No new runtime value law is added.

KMX patch: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
The exact three KMX inputs are hash-checked by PCB_gate.py. These scalar packets do
not call a copy builtin, so they grant no new copy-dependent native credit.

Runtime boundaries for remaining helpers: PDA replies are quantified op38, digest
realization is existing RuntimeSha256Value, return-data values/clear retain the
existing RuntimeReturnData/RuntimeReturnDataClear domains. Native slice/seed/program/
reply association is still required. No syscall implementation will be unwound.

No selected harness writes static state. Existing unrelated frozen cfg(kani)
static-mut warnings are not reached by246. No Option<fn>-dependent credit is claimed.
