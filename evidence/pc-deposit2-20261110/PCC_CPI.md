# Returning CPI obligations

POOL:356 and nested POOL:357 OPEN. No native bridge/control has run. PCC_RuntimeCpiAccountView transcribes the lead-added (c-a) row with clause 1 keyed on instruction metas M. The two compiled view lemmas will not establish guard counters, key/flag/handle/Rc identity, token semantics, system semantics or success. Passed cells remain arbitrary.

PCC-CpiHeaders in PCC_LINKAGE.md is separate. NIZ_LAYOUT.deposit_separate and NIZ K011/K012 are retained prerequisites, not repeated or promoted to a native call association. Full uniqueness, reached key/cell identity and exact tokenStart remain caller obligations.

Pinned SDK inspection: solana_program 2.3.0 program.rs invoke delegates to invoke_signed with empty seeds. invoke_signed checks each meta against the first matching info in source order; writable metas try mutable lamports then mutable data; other metas shared lamports then shared data. Each `let _ = ...?` temporary drops before the next statement. Missing infos are skipped here, not invented as an SDK error. On success the unchecked call forwards exact instruction, infos and signer seed groups. Deployed target then enters solana-cpi 2.2.1 StableInstruction and sol_invoke_signed_rust. These are source observations, not native certificates.

Reply handling must retain the actual conversion: raw status 0 gives Ok; other statuses pass through ProgramError::from(u64). Arbitrary high unrecognised statuses truncate to Custom(u32) in the pinned SDK; their ABI image need not equal the raw status. PCC_ErrorDecode models this conversion instead of assuming an unrestricted identity law. No runtime status-domain restriction is introduced.

System create_or_allocate_pda gets Rent::get before entering its rent helper. That helper repeats payer/system validation, rejects nonempty/non-system target, computes minimum_balance(exact_bytes).max(1), clones infos [payer,target,system], wraps seeds once, then create_account on zero lamports, or optional transfer followed by allocate then assign. Every returned error propagates and stops its suffix. Generic Rent floating arithmetic, lamports getter/drop and all builders remain obligations; assuming default Rent would strengthen the caller domain without justification.

RuntimeCpiReadonlyEntry7 is PENDING and unused. op38 remains quantified. No runtime trust row beyond the lead-approved (c-a) is introduced.
