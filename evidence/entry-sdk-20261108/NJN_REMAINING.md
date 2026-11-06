# NJN remaining obligations

Target not yet established. This is an incomplete SDK-law return, with no row
promotion and no new trust. The final budget accounting is in NJN_HANDOFF and
NJN_ATTEMPTS. Unspent formal allowance is not reported as exhaustion.

## Required law members and why no complete certificate can be replayed

1. Shared AccountInfo::try_borrow_data: native exact-call wrappers and safe
   pre-state partitions are not a theorem relating every actual Ref carrier to
   the owned reference. The one all-reference extraction failed at drop and
   emitted no Lean definitions. Therefore extract(f_ref)=law cannot be stated
   against an emitted definition. Remaining: fixed/split emission under a new
   allowance, full typed identity and footprint, caller bound on live tokens.
2. Exclusive try_borrow_mut_data: same emission gap; the actual returned RefMut
   must identify the SAME counter/payload through movement and dereference,
   including conflicting borrows and exact Err. Bounded safe constructor
   preflights do not become a universal SDK contract. Remaining is native plus
   reference emission, not an additional counter arithmetic lemma.
3. Ref/RefMut deref/move/drop: the hand model's complete token-consumption,
   payload/frame, current-counter and round-trip laws are checked. Full native
   carrier interpretation and extract(f_ref) remain missing. No raw integer
   guard fabrication, P7 name citation or initial admission can replace them.
4. Three-account TX1 exclusive-copy ABI: one-window native/canonical KMX
   composition cannot identify all three real account handles, returned guard
   and snapshot producer with the admitted heap. That is still a native SDK/
   caller association obligation plus the missing reference emission. No
   additional Lean-only range induction remains: copy_range and its complete
   frame/drop consequences are proved over KMX's induction.
5. Seven-account TX2 acquisition/cleanup ABI: no complete seven-handle
   source/native relation or implicit cleanup/error-suffix certificate is
   supplied. The primitive laws do not establish that relation. Native methods
   and full emitted reference are needed; further symbolic frame wrappers alone
   would hide that gap.
6. Clock::get: mathematical five-field Ok/Err/status/error-conversion/frame and
   successful-slot binding laws are checked. Native concrete converter support
   is separate from the actual SDK output allocation, syscall callsite, raw
   reply/status association and frame. The unchanged syscall signature supplies
   no harness-local log argument; a proper source-erased native cut is still
   needed under rule16. Host/deployed cfg paths must be certified separately.
   No additional trust row or success assumption is allowed. Emission is also
   absent because the single job extraction aborted before emitting any root.
7. Pubkey::create_program_address: native concrete PubkeyError conversion is
   supported. Deployed seed count/length checks, ordered slice descriptors,
   program id, output region and raw status/reply forwarding are unbridged.
   Host SHA/curve computation is a different body and was not unwound. Unsupported
   status≥3 abort is retained. op38 is arbitrary; no address-value law is needed.
   This needs the deployed native cut and emitted reference, not a PDA value axiom.
8. Eligible NJD cuts: none waits only on a COMPLETE new law in this return.
   Replacing SDK calls with the unchecked hand-model laws would assume the
   missing association. Thus no legal rerun is performed and NJD_K038 is untouched.

The extracted-reference gate cannot be completed with the remaining Lean or
Kani allowance: there is no emitted object to prove equal, and the only
extraction is consumed. Further scalar proofs do not discharge that gate.
Native supporting members continue independently wherever they have an
admissible split; this document does not claim they were impossible or that
unused allowance itself justifies success. No formal-only claim is left open
merely because a native budget is exhausted.

## Each of the fifteen OPEN entry occurrences

| Occurrence | Exact remaining dependency / disposition |
|---|---|
| TX1:330 entry | TX1:333 process OPEN; waits on driver spine under(as). |
| TX1:333 process | TX1:344 stage1 and TX2:240 stage2 OPEN; cannot assume their complete Results. |
| TX1:344 stage1 | TX1:345 owned child OPEN, full three-account SDK and copy ABI above. |
| TX1:345 stage1_owned | TX1:328 first_decoded OPEN; full source-ordered cut/frame/cleanup remains. |
| TX1:328 first_decoded | TX1:094 verifier::tx1 OPEN, owned by the driver lane. |
| TX2:213 entry | TX2:221 process OPEN; same bottom-up exclusion. |
| TX2:221 process | TX2:240 stage2 OPEN and primitive binding. |
| TX2:240 stage2 | TX2:241 owned child OPEN, seven-account ABI and actual Clock association above. |
| TX2:241 stage2_owned | TX2:242 validate_asq8 OPEN; complete Result, heap and cleanup not supplied by observer closure. |
| TX2:216 decode_checkpoint_box | TX2:152 decoder OPEN outside this job; no successful Box premise permitted. |
| TX2:218 decode_master_box | TX2:153 decoder OPEN outside this job; allocator trust does not certify decoded value. |
| TX2:217 decode_lane_from_pool_release | Full header/range/iterator/zero-tail and Box cleanup remain; NJH iterator support is not op50 closure. Outside the ordered SDK-law scope. |
| TX2:233 authenticate_asq8_accounts | Checkpoint/master/lane/registry children OPEN and deployed PDA association missing. |
| TX2:234 authenticate_invariant_release_registry | V1 registry/entry decoders TX2:203/201 OPEN outside job; SAME-record and PDA frames also pending. |
| TX2:242 validate_asq8 | TX2:233 authentication OPEN; CLOSED independent children do not discharge it. |

TX1:329/TX2:212 observers are already CLOSED at ledger14 and are not rerun.
No sessionA or sibling worktree is touched. No headline assumption discharged,
no source adoption or cold release replay, no shipped source/artifact change.

## Global ownership invariant (NJN-F2)

The current local Live predicate is insufficient as the complete validity
domain: it permits two local exclusive tokens at different indices for one
cell at counter -1. The required global ledger must exclude that state and tie
the counter to ALL owned live tokens. Public Rust reference constructors also
need that explicit validity domain. No caller or native contract uses Live as
an SDK ownership premise here, so no admitted result depends on that mistake.
Before a complete library law, prove global ledger preservation and connect it
to actual native typed guards. The present hand-model frame/transition equations
remain true on their stated terms, but do not settle that preservation.

Final allowance:70/70 native,30/70 formal,1/1 extraction. Eight native timeouts
are retained. The direct Borsh window and Clock default-region initialization
have controls, but the full Borsh contract and Clock syscall association do not.
K016/K017 leave large-payload conflict/ownership frames open. The remaining
concrete statements require missing emitted full-carrier definitions AND native
same-heap/guard/syscall associations. Generic extra hand-model lemmas cannot
serve those equalities. The global domain remains an explicit specification
shortfall: no claim is made that mathematical ledger preservation is impossible,
or that a failed extraction proves it. The return is incomplete, with the
member-by-member non-closure reasons above, rather than a completed task or
formal-budget exhaustion. No unspent allowance licenses a second extraction,
a third full combined audit, or assumptions standing in for the missing law.
