# NJH laws

Target not yet established. Support lemmas are not row credit.

* Observer: AspisR1.NJH_Observer.emitted proves canonical emitted AdapterRw.observer equals the constant model None, for every Ops. It has no hypotheses beyond the unused Ops parameter, no axioms, and no native function-pointer assertion. NEF source certificate and mutation replay bind frozen cfg-constant None and deployed graph. NJH-F1 discloses that NIV_L022 itself omitted the observer declaration.
* Borrow: NJH_Ref is the one pinned NCO extraction of NJH_reference.rs. NJH_BorrowLaws gives complete successful/negative/saturated shared branches, exclusive success/error and exclusive drop. NJH_BorrowCounters gives the no-wrap mathematical transition. These references are not actual RefCell memory certification.
* Copy: NJH_CopyWindow gives selected-coordinate and outside-coordinate laws and extensional composition. It does not assert native copy correctness or exclusive ownership.
* Clock: NJH_SyscallLaws.clock_ok/clock_error preserve every Clock field or the full raw status, and clock_frame retains abstract state/events. Actual ProgramError conversion, ABI output initialization, syscall frames and guard cleanup remain native obligations; RuntimeClockSlotBinding supplies only the successful slot.
* PDA: pda_ok/pda_error forward bytes/status only. They assert no address value. NJH_PDA_PROPOSAL is unused and awaits lead decision.

No reference-domain restriction is promoted to a caller-established fact without a matching proof. No new trust row, XRn kit, multiplication proof, SHA unwind, writable static or quarantined Option<fn> verdict is used.
