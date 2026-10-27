# Remaining direct-extraction experiment

The direct records body fails in Aeneas branch joining at source230 under the current optimized-MIR setting. Charon documents that its optimized setting disables optimizations. The next source-preserving experiment requests rustc MIR optimization level4 and inline-mir explicitly, retaining precise/desugared drops and the same production source. This changes compiler preprocessing, not the Rust body or extractor implementation. It must produce a fresh pinned receipt and pass the unchanged Aeneas translation and Lean checks before adoption. No hand-edited LLBC projection is accepted as an extraction of shipped records.

A separate exact Kani harness now compares the actual root helper on both sides rather than a literal expected root table. This has no stubs, nondeterministic inputs or assumed helper equalities. It is prepared only; no verification credit.

Read-only inspection of the retained Charon source found driver.rs:set_mir_options forcibly resets mir_opt_level to0 after command-line parsing. Therefore the prepared level4-only command would not test the intended change and has not been run. The next command explicitly enables the named standard rustc passes Inline, GVN and CopyProp, plus inline-mir. No extractor binary/source is modified. Its emitted body must differ before an Aeneas rerun is justified.

The inspected driver.rs SHA256 is41e7a384d484fc31603578086d273a61f15ea0d3ba76ff534805435a47aafa84. Its set_mir_options assigns mir_opt_level=Some(0) but only explicitly disables CheckAlignment/CheckNull passes. CLI flags for the named passes remain an experiment requiring emitted-body inspection, not a claim that optimization succeeded.
