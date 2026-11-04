# NFH slice S composition

**96/97 rows,126/129 edges,6/7 roots CLOSED; no new composed credit.**
The sole OPEN member/root is scan_proof_buffer, TX2:226. The seven-root target
and deployed100-bit per-attempt target remain NOT ESTABLISHED.

All NFD and earlier CLOSED certificates are imported read-only without re-proving
them. NFH_EDGES.json is byte-identical to NFD_EDGES.json. NFH_LEDGER_DELTA.json
adds no certificates or trust. NFH_validate.py runs the inherited additive
NDT/NED/…/NFD composition unchanged and adds exact frozen comparison-instruction
and OPEN-status checks. The native support NFD_K134–150 retains zero root/edge
credit. There is no NFH scanner certificate to present as “Validator root closed.”

## What is established

Inspection of BOTH hash-checked release ELFs identifies the688-byte comparison
wrapper0x1749d0 and its0x1749e8 relocation to the undefined runtime symbol
sol_memcmp_. NFH_COMPARISON_FINDING.md records the two scanner-shaped call sites,
exact input registers/length/output slot, zero test, features, sysroot source
path, source-association limits of the stripped ELF, and smallest outside-slice
obligation. Full disassemblies are retained as.xz plus uncompressed.sha256;
no ELF/binary is committed. This is static inspection, not a new Kani proof.

NFH_ComparisonBoundary.lean, accepted NFH_L004, proves:

```lean
def ZeroLaw (left right : List U8) (reply : Int) : Prop :=
  reply = 0 ↔ left = right

theorem reply_eq_loop (left right : List U8) (reply : Int)
    (runtimeZeroLaw : ZeroLaw left right reply) :
    decide (reply = 0) = NEU_EqualityLoop.equalBytes left right

theorem zeroLaw_necessary (left right : List U8) (reply : Int)
    (association : decide (reply = 0) = NEU_EqualityLoop.equalBytes left right) :
    ZeroLaw left right reply

theorem opaque_reply_insufficient (left : List U8) :
    ∃ reply : Int, ¬ ZeroLaw left left reply
```

These SUPPORT the explicit boundary diagnosis. The inherited byte-loop induction
is reused; no large recurrence is evaluated. The first two printed axioms are
[propext]; the third uses [propext,Classical.choice,Quot.sound]. L004 exit0,
wall2.192365279s,peakRSS5,337,552KiB,swap0,-M7000 in an admitted6G/8G/Swap0/Tasks64
scope. Complete revision/target/argv/source/dependency/Aeneas pins and all six
attempts' section6 fields are retained. L001–003 failed elaboration, have no
credit, and their sorryAx diagnostics are explicitly excluded. Final source
has no sorry/axiom/admit/native_decide declaration or heartbeat/depth override.
This ordinary#print axioms audit is summary-based, not a raw NEP release audit.

## What is retained and what remains

NFD_ScanConditional.result_state_effects still requires
nativeEqualityBridge : NativeEqualityAssociation equality. No NFH theorem
instantiates it. The runtime syscall body is absent from both release ELFs, and
a host intrinsic/byte-loop proof would not identify that deployed runtime body.
RuntimeMemcmp688Zero is a PROPOSAL, not adopted trust. Its state/normal-return
conditions and the alternative pinned-runtime extraction packet are explicit in
the finding. No PhysicalInterpretation/(ab) reclassification is used to hide it.
The three scanner call-domain certificates and root certificate stay UNISSUED.
NFH_REMAINING.md gives every remaining obligation and the under80% budget audit.

Headline AspisR1.RPx_Deployed.deployed, frozen3,L154 parameter,D188 narrowed,
privacy and two-transaction contract remain unchanged. P6/D188 optionA remains
reclassification, not removal. Existing RuntimeReturnData(ab) has one inherited
CLOSED emitter native use and ZERO new NFH uses. No new trust or(ab) use.

No shipped source or existing proved module changed; no ELF rebuild trigger.
Default/devnet pins were freshly checked, Pool pin121f3e29… is inherited rather
than rebuilt. All commits remain local. Cache imports are copied and hashed;
no sibling/session-A workspace, key, wallet or source was modified.

## Explicit688-domain conversion

NFH_ComparisonDomain.complete688_on_domain and complete688_association (L005)
show how a runtime law scoped ONLY to two688-byte lists can supply NFD_s
universal mathematical equality interface: complete688 uses the runtime zero
test on-domain and the existing loop off-domain. Both axioms:[propext].
This conditional completion is not the actual native comparison function; its
use requires caller-established lengths for the SAME two live buffers, plus
At688Law as a named unproved runtime hypothesis. No native or root credit.
NFH_L006 is one final ordinary#print axioms audit of all five support theorems
on the combined import,standard subset only. No raw NEP audit was claimed.

Final additive validation exit0;71 tests passed (60 inherited and11 new,with
per-instruction and per-promotion subtests). No additional model changes were
made after that replay;the added domain support has no ledger certificate.
