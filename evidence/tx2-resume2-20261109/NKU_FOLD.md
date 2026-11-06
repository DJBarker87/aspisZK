# NKU parent fold

Target not yet established. The parent carrier is NKU.State (NKU_State.lean), with one Frame containing the fixed checkpoint/proof/public slices and SAME Reservation; decoded slots, Reader/backing, iterator, owned Vec and full terminal status remain in this carrier.

Events: NKU.Event.call wraps all nine NJU_ResumeObserved event constructors, covering all 45 top-level and nested NKK occurrences; terminal and cleanup are separate parent observations. No new primitive Reader domain is introduced.

NHZ_DRIVER.Cuts uses Code/SdkC_Source.Log, whereas resume uses NJU_Log.Run and NJU_ResumeObserved.Event. A local bind/frame/terminal algebra of the same shape is needed; it must retain fail/div and Rust Err prefixes without suffix.

Status: state defined (pending compile); header first; digests 2–4, roots 5–7, fields 8–12, queries 13–34, validator 35, semantic 36, z/claim 37–43, filled 44, weights 45, tail/Box/pair/cleanup all OPEN. Native component positives/controls are reused only as pinned inputs, never counted as parent closure.

Passing installation: NKU_HeaderStep.source and NKU_Front.source (header1 plus digest2–4, with source suffix explicit). The digest join is NKU_DigestJoin.source. Passing local state steps: NKU_Roots, NKU_Gamma, NKU_QueryFirst/Mid/End, NKU_Validator, NKU_Semantic, NKU_ZClaim, NKU_Allocation, NKU_Weights. Passing terminal helpers: NKU_Array22.source, NKU_Tail.guard_reject. Source-to-state suffix assembly is active; local steps alone do not count as TX2:124 closure.
