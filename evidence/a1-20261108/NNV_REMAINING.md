# A1 at the corrected literal host

Target not yet established. This job closes no ledger row.

Exact parent (all original binders and universal adversary retained):
`RSL.TAS.NND_A1 (AspisR1.NNH_Run5bHost.S_host L0 copy std)
 NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C`.

1. Scan / semantic Verified: scan is linked in both directions at length 57607
   (NNV_CurrentScan, NNV_ScanWeakErr). The semantic parse/public-transcript/begin
   return ports pass. OPEN: transport NNH_FinishReturns.value through the fixed
   FinishModel.finish, at the same returned prefix/challenges/transcript, then
   associate its Verified output with LIBC_PreparedCarriers.verified. This is
   Lean-only, not a Kani or decoder-liveness requirement.
2. Prepared input/output ports: NNV_PreparedNative.returned supplies the exact
   fixed host op8 reply and scratch, from the SAME canonical P returned law;
   NNV_PreparedDomainPorts transports the unchanged domain. OPEN at its caller:
   derive the SAME semantic/View/scratch from the prepare front, including
   Filled, both expansion outputs, View and semantic finish; no free native
   success or representation premise may replace this.
3. Geometry/query/batch/checkpoint continuations: the local outer geometry
   transport and current returned geometry port are CLOSED (L040-L043, L045),
   on the SAME queries and canonical raw indices. OPEN: actual query
   installation association at the SAME prepared/accumulator/g/geometry/pending;
   batch call at SAME roots and digest; flush and checkpoint association at
   SAME accumulator. Prepared state transport passes L039. Checkpoint digest/erasure pass L046/L047;
   decoder P1880 ports pass L048. Their full caller continuations remain open. These are Lean-only.
4. Common/afterstate: NNV_CommonAssociation uses the existing source common
   theorem plus the decoder inverse; it proves the candidate-afterstate
   projection too. OPEN: complete adapter getter/common diagram at the body
   continuation, then consume encoder ports without nominal-variant rewrites.
5. 328/345 composition: the SAME decoder witness supplies P1880 and original
   R4/094/087 domains (NNH_Run5bA1Domain; NNV_DecodeP1880 reindexes the ports).
   OPEN: full common/body composition through owned source and current child.
6. Global weak Err: scan has the local non-Ok implication. OPEN: model1 Ok
   implies canonical evaluator Ok through every composed body continuation.
   Local ReturnedGraph.not_ok and scan do not establish this global claim.
7. Assembly: blocked by 1-6; no A1 term, conditional G0, or row credit delivered.

Weak Err BEFORE: returned RSL Err -> exists pe, model1 = ok (Err pe).
AFTER: returned RSL Err -> not exists saved, model1 = ok (Ok saved).
The owner-approved NNH_AcceptanceSig/NNH_RecordSig restatement changes no Ok
arm, carrier or quantifier, and requires no exact error payload or liveness.

First unclosed semantic association (all variables universally quantified at
the corrected context; this is an OPEN goal, not a new theorem hypothesis):

```lean
NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ (envOf c) = .ok sem →
(DrvC_Installation.currentInstalled (configuration c)).op9
  (NNV_PreparedAtHost.digest c)
  (AspisR1CurrentCaller.FirstComposition.toCurrentPublic pub) bytes () none =
.ok (.Ok (NNV_PreparedInputs.sem sem))
```

NNV_SemanticPrefix.returned proves the parse/public-transcript/begin prefix,
but still carries NNH_FinishReturns.value at the same prefix/challenges/
transcript. The missing continuation is the fixed FinishModel.finish result
and its complete Verified fields, not hash injectivity or parser liveness.

L044 exposed the overbroad arbitrary-Usize roundtrip to LIBC_Usize.raw.
L045 instead states equality at exactly LIBC_Usize.raw start/stop, matching
LIBC_Geometry.model's natural-number arguments for ALL naturals. No bound or
representation premise is added. At deployed 0/10 the ordinary small numeral
conversion supplies the current source indices.

Budget exhausted: 50/50 scopes. Remaining members 1-7 are Lean-only; none is
blocked on Kani. No fresh host scope or unchanged regression is authorized.
