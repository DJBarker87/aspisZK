# Executable initial-message image and distance recovery

`GSInitialMessageCandidateFilter.filterCandidates_mem_iff` ties the actual coefficient-list image filter to the polynomial-root contract, using the existing generic initial encoder degree bound. It handles coefficient-list-to-CPolynomial equality explicitly.

The concrete runtime initial encoder evaluates the actual CPolynomial at the literal stored stereographic point with the retained degree-512 multiplier. Its executable distance predicate counts actual coordinate agreement. `GSInitialActualMessageRecovery.initial_runtime_close_list_mem_iff` proves that its runtime candidate list contains exactly the messages with released initial agreement at least 38230, assuming the actual interpolation witness and root Candidates contract.

The mathematical exact initial encoder appears only in the specification and proof. Runtime definitions are ordinary executable Lean; they do not call a noncomputable GRS record. The fixed WideExact consumers use canonical instances; no arbitrary local Field structure is assumed.

All three focused native NUC Lean 4.32 targets passed, with bounded cgroups, zero swap and standard-only axiom reports. Exact source/import/object pins, revisions, commands, wall times, GNU maximum RSS and resource samples are retained. Native objects are archived for reuse. Existing inverse/filter owners were reused or compiled only where their native objects were missing; no full manifest replay was run.

The caller still must prove that actual interpolation/root calls supply these witness/Candidates premises, then compose all lanes through the joint-list merge and actual witness scanner. Full extractor cost, completed-log fixation, acceptance/commitment coupling, protocol/ROM/source/runtime soundness, privacy and transaction release gates remain open. This component result is not the 100-bit spend theorem.
