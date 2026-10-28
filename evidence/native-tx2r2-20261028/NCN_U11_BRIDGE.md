# NCN U11 continuation

U11 OPEN; deployed target not yet established. Inherit NCI_U11_BRIDGE.md and
all its scoped results; no NCI fact is reproved or broadened.

## Stage 1: full checkpoint raw windows

NCN_K001/K002, K003/K004, K005/K006 establish the actual frozen Reader::raw
for widths 1, 4 and 16, arbitrary 1768-byte source, arbitrary bounded cursor,
and arbitrary observed return/source-frame byte. Cursor, source pointer and
length are retained. Matched opposite-byte controls fail under the identical
KMX configuration. These are native source-helper windows, not resume closure.
The KMX patch remains exactly bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

NCN_K007: width32 timed out at 90 seconds; zero credit. K008 was not launched.
Do not repeat it unchanged. Next decomposition: one observed byte/half at fixed
return offset, plus KMX region/frame composition; no cap or timeout increase.
Widths16 and below now remove the earlier 64-byte-only allocation restriction
for those actual raw operations. Width32, caller installation, scalar Result
association, iteration and ownership still remain open. Full raw width32 must
not be inferred from width16 by changing the frozen helper's call pattern.

No cryptographic assumption, native model carrier, security game or metric
changed. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 unchanged in repo.
Exact commands/pins/exit/wall/RSS/swap are in NCN_ATTEMPTS.jsonl and receipts;
Kani axioms: not applicable. No ELF build trigger occurred.

## Stage 2: width32 split and Result contracts

NCN_K016/K017 and K018/K019 close the actual raw32 windows on the prefix
class 80+32*i (i<7) and tail class 632+32*i (i<2), respectively. Arbitrary
source/returned byte, source frame, pointer and cursor are checked as above.
This exact nine-site cover replaces the timed-out arbitrary-cursor shape;
it does not assert arbitrary-cursor raw32 totality.

NCN_K020 inverted ensures FAIL and K021 modifies violation FAIL are the first
two Result<K,Error> fidelity controls. NCN_K022 proves the actual Reader::k
weak cursor contract on the full1768 allocation: bounded cursor advances16,
including Err. NCN_K023 real zero-byte call is Ok. NCN_K024 cannot codegen
stub_verified because QM31/Error lack Arbitrary; no native credit. The owned
scratch repair adds cfg(kani)-only Arbitrary derives to the three field records
and Error. No repository shipped file is modified, and no source-body or domain
is changed. The unimplied-under-stub and call-site cursor controls remain pending.
A weak cursor contract never supplies byte or canonical-output correspondence.

## Stage 3: arbitrary iteration and ten-read call order

NCN_K025 supplies the third Result fidelity control: is_ok on real zero bytes
passes at K023 and fails under stub_verified at K025. K026/K027 are the weak
cursor call-site pass/failing control. This contract carries only cursor+16
and its modifies frame, never a byte/result equation. Derive repairs are
scratch-only; K024 remains excluded, not renamed.

NCN_K032–K041: five matched pairs establish one native mutable suffix-iterator
step over arbitrary64-cell pre-state and arbitrary i<64: cursor at712+16*i,
exact writeback of the SAME returned K (ghost reply log), arbitrary other-cell
frame, unchanged target on Err, and remaining iterator length63-i. The native
step uses the actual Reader::k contract, with full1768 backing. Ghost logs
contain Option<K>, never Option<fn>. Erasing the two ghost writes restores the
frozen four-statement loop body, pinned in NCN_WEIGHT_SOURCE.json. Borrowed
slice iteration is established; full Vec allocation/ownership/cleanup and its
same-buffer association remain lower obligations, not silently inferred.

NCN_K042–K047: the actual ten-read helper, with erased reply/cursor observation
wrappers and stub_verified Reader::k, has exact408+16*j ordered calls, successful
return values identical to each corresponding reply, final568, and first-error
short circuit. The full checkpoint is arbitrary, replacing NCI's sparse input
class. The weak contract quantifies over more replies than real decoding, so
this is call-site transport parametric in the real lower reply; byte/decode
identity must still be supplied by the CLOSED raw/codec child association.
No fictitious suffix call or independently selected output is assumed.

NCN_L007 proves NCN_WeightErrors.loop_error, the missing generic mutable-loop
error induction. It uses the real selected mutable iterator and existing
replace_slot lemma. Axioms [propext, Quot.sound]. L004–L006 were rejected proof
drafts and their sorryAx audits are explicitly excluded. L003 proves all nine
raw32 cursor-domain classes and the no-overflow addition domain, standard axioms
only; L002 was a rejected list-case split, not an accepted audit.

Still OPEN: native Vec owner/allocation association, full query contains-prefix
association, resume/proof/public/syscall/same-save pairing and all parent
installations. This stage removes the sparse64-byte and one-slot limitations
from the stated native windows; it does not close U11 or the deployed theorem.

## Slice-returning contract limitation and model totality

K048 inverted-ensures FAIL; K049 modifies violation FAIL; K050 weak length
contract PASS; K051 real byte-implied assertion PASS. K052 stub_unimplied is
CODEGEN-FAILED: `&[u8]` does not implement kani::Arbitrary. K053/K054 are unrun.
The required third fidelity control did not execute, so this slice-returning
shape is NOT admitted for call-site composition. No pointer-word output carrier,
foreign reference fabrication, unsafe Arbitrary impl or renamed harness is used.
This is an interface limitation, not a proved source bug or a host fault.
The direct raw/iterator window route remains available independently.

NCN_ReaderTotal.section_total (L010) proves every bounded scalar section returns
Ok with either decoded values or the first checkpoint error; it does not assume
native/model equality. NCN_WeightTotal.loop_total/weights_total (L011) compose
existing successful writeback induction and the new error induction, obtaining
the exact selected readWeights totality for every bounded Vec length, hence64
at cursor712 in a1768-byte checkpoint. Only standard axioms. L008/L009 were
rejected drafts; their sorryAx audits are excluded.

NCN_QueryDecision.accepts_iff, append and reject_at (L013) give exact acceptance
conditions and first bad-prefix rejection for the selected model queryLoop,
reusing NCI's forward invariants. This is useful for native-step composition;
it is not the missing native contains-prefix/Std association. L012 was a
rejected propositional proof draft; its audit is excluded.

## Final native prefix and query status

K069 WHOLE resume on arbitrary checkpoint/proof/public mismatch inputs timed
out90s. It has zero credit. K070–K075 instead prove/control only the exact
frozen header+hash PREFIX, byte-pinned in NCN_PREFIX_SOURCE.json. The same
harness names are retained but the target explicitly changes to the prefix
Result<(),Error>, with no post-hash continuation. It is not a whole-resume pass.
The complete proof57607/public1880/checkpoint1768 contents are arbitrary;
proof→public→checksum short circuit, request pointers/lengths and checksum
prefix1736/domain are checked. Earlier matching replies equal the stored slot;
the first differing reply is arbitrary with an arbitrary mismatching-byte
witness. NCN_MismatchWitness.mismatch_witness (L014) proves this covers every
unequal same-length reply, rather than a single-bit corruption class. Digest
VALUE and the actual SolanaDigest/syscall forwarding remain the existing U00
runtime boundary, never a SHA implementation in Kani.

K067 arbitrary-prefix out-of-range query step timed out. K076 split that shape
with an unreachable-contains sentinel, but its first stub signature lacked the
generic parameter and codegen failed. The OWN cfg-only stub repair at K077
retains the harness name, adds T:PartialEq, and passes with the sentinel proved
unreachable. **K077 HAS NO NATIVE CREDIT**: the matching negative control under
that generic-stub configuration was not run before70/70 exhaustion. The trap
has no promised semantics for any reached contains call. It must not replace
contains in the live in-range/duplicate cases. The next worker must run the
matching negative before relying even on this rejection class.

| Member | Final native/cohort scope and remaining implementation work |
|---|---|
| F107 Reader::raw | Local full1768 windows for widths1/4/16 and all nine reached32-byte cursor classes pass with controls. Native account/saved-buffer region and enclosing operation installation remain OPEN; generic arbitrary-cursor raw32 is not claimed. |
| F106 Reader::k | Full1768 bounded weak cursor contract admitted with Result controls; exact codec/raw child results reused. SAME-byte/source-to-installed-reader carrier association remains explicit, not supplied by that weak contract. |
| F105 Reader::e | Exact raw32 reached-domain windows plus old closed decoder results; enclosing native reader/callee installation and saved-region association remain OPEN. |
| F121 read_checkpoint_semantic_alpha | Complete native ten-call transport on arbitrary full checkpoint and all reply/error prefixes; corresponding model sections reused. Full same-byte Reader::k association/installed-port composition remains conditional. |
| F122 read_checkpoint_weights | Arbitrary64-cell native iterator/writeback/reply/frame/error step and total successful/error model induction are checked. FilledK64 plus actual Vec borrow/deref/cleanup, same source-buffer ownership and enclosing loop association remain OPEN. |
| F126 validate_checkpoint_queries | Exact model decision/first-error algebra checked. Native contains-prefix association and full outer22-step association remain OPEN; K077 is unpaired and unusable for native credit. |
| F124 resume | Header/hash prefix only. Arbitrary accepted full result, allocation/Box/Vec ownership, all installed reader/validator ports, actual proof/public/saved provenance, syscall forwarding and native next10 caller association remain OPEN. |

All remaining rows require native memory/iterator/call-site association or a
named open lower bridge. Repackaging them as a whole-output equation in Lean
would not discharge them. Native/body/source-to-ELF trust, RuntimePersistence,
L154 statement parameter, narrowed D188 and RPx_Deployed.deployed are unchanged.
The coherent dictionary's digest/error slots remain op43/op44.

Final evidence summary:70/70 Kani and24/70 Lean;77-theorem co-import/axioms
audit L024 passes with standard axioms. All94 scopes terminal and pins unchanged.
For member-by-member reasons why remaining work needs native evidence despite
unused Lean attempts, see NCN_HANDOFF.md. No enclosing U11 closure is claimed.
