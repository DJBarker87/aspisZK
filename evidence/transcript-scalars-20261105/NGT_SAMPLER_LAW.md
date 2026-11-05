# Same-execution sampler law for NGN

Use NGT_COMBINED_IMPORT.lean with NGK_COMBINED_IMPORT and the retained exports.
NGT_CallerInterface.scalar is the S1–S4 interface for arbitrary base sampling:

    PreparedModel.scalar (withCandidateSamplers sampling) D before row payload mode
      = ok (nativeOut, {before with state := thirdReply})

The hypotheses are three LOCAL digest observations on the same original state,
row and payload (NGT_BlockAssociation.observed constructs the block witness),
and the native local reduction trace at secondReply. They are constructed by
the staged native certificates and existing Lean inductions. No whole sampler
Result equation, arbitrary next transcript state or independently chosen output
is a hypothesis. Gamma's low quotient, addend bounds, canonical decode domain
and second carry=false are derived on those SAME traces.

NGT_CallerInterface.scalar_k has the corresponding exact rho law with
withSourceFromQm sampling. An arbitrary fromQm field is not a model of the actual
frozen constructor; its source implementation is fixed by the existing closed
PreparedFromQmSourceBridge packet. The four-pass native trace and its returned
four coordinates identify the complete sampled QM31, not merely a residue class.

NGT_FrameChain.scalar/scalar_k additionally expose unchanged hash and all three
ordered digest input/reply pairs. Read [1] and advance [2] both use the SAME
absorbed state; advance never uses the sampled block. Runtime values are supplied
by the already accepted P1/RuntimeSyscall rows, while NGC forwarding identifies
exact input descriptors and unchanged reply. No oracle schedule is rearranged.

Native root domain: valid live shared payload and transcript borrows, row<=95,
length<=2048. The explicit source call rows27..32 and lengths928/32/224/256/0
are covered; the requested2048 width is also covered. Arbitrary bytes are allowed
at every position. NGT_RuntimeDomain supplies29 and64 window inductions for928
and2048 bytes, with the generic disjoint-memory frame. The runtime packet has
strictly wider bounds:9 parts, each<=57607; absorb uses4 and read/advance2.

NGT_CallerInterface.gamma_powers instantiates NGN_ScalarDomains.gamma_powers
on the SAME returned gamma and next state. NGN must still associate its actual
stage inputs with these caller domains and install the independent query and
prepared_claim packets. Queries remain NGQ-owned; no query proof was duplicated.
