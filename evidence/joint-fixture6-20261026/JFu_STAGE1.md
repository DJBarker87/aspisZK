# Stage 1: header, source initializer equation, executable diagnostic

JFu_PublicHeader.header checks the retained ASF8 prefix/length in the kernel.
JFu_TranscriptSeed.public_source proves the emitted public_transcript returns
exactly the hash of the semantic serializer output and c1_root, with row zero.
Its serializer/length/digest premises remain explicit; it does NOT supply the
real decoded public instance. JFu_PublicProbe executes the emitted decoder on
retained public1880 and reports acceptance; this is a diagnostic, not a kernel
certificate and receives no premise-removal credit.

JFu_InitialAudit (002) now successfully audits the prior composed fixture roots,
new installation and current Rc7 top. All successful theorem audits contain only
standard axioms; failing elaboration recovery output is not accepted.
