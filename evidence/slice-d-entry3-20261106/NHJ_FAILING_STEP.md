# Failing steps

L002: own runner generated a nonexistent NHJ_NGK_exports_20261106 lookup while adapting the prefix. Direct-import object preflight stopped before Lean submission, so no proof ran. Corrected the own input path to retained NHD_NGK_exports_20261106; validation stays strict. L004 is the corrected first combined compile, not a timed-out or passing-shape rerun.

L007: own storage_domain proof treated a disjunction as a product. Elaboration fails; the resulting sorryAx diagnostic is rejected, never imported as credit. L008 cases the three actual storage constructors and proves the exact two-error domain.

L011: own result annotation used PE.AccountBorrowFailed through an abbrev, which is not a namespace. Elaboration fails and the sorryAx diagnostic is excluded. Corrected the constructor namespace in L012. No tool/cap change.

L016: own distinct packet referenced an Account abbreviation from a module it did not import. Corrected to the actually imported NGL_DistinctStep.Account and supplied local classical decidability, without changing any predecessor module. L017 is the corrected focused input.

K011: combined actual SDK guard + arbitrary copy-header result at128 bytes, complete frame, metadata and selected source byte timed out at the90-second harness limit (106.214s total, peak6,345,568KiB, swap0). No control or pass credited. Split replacement: borrowed admitted-header/ownership return without SDK; SDK bracket separately by existing typed guard law and isolated native bracket. No unchanged run or increased cap. Own NHJ_tmp solver pattern cleanup found no residual files.

L020 inspection requested a nonexistent Vec.from_slice print; this is an own inspection-name error, not a model or proof result. Corrected L021 inspects the actual Slice.clone used by to_vec.

L025: canonical error type alias does not re-export constructors under the alias namespace. Own name-retarget input error, fixed by qualifying only the27 constructor occurrences with NGL_MetaReference.ProgramError (same NGL canonical-owner method). The clone function and snapshot control remain byte-identical modulo qualification; exact diff/pins retained. Failed generated declaration diagnostics are excluded from credit.

K014: full58295 fresh allocation + selected-window logging timed out (94.407s total, peak5,122,544KiB, swap0). No credit/control submitted for that failed shape. K015 splits at the after-copy continuation: the arbitrary full Vec reply is already a legal pre-state allocation; no payload indexing or fresh allocation inside the continuation. Its existing-buffer frame plus pointer/len/cap transport is checked natively. K015 PASS; matched payload-write control pending. This is a genuine staged-cut/pre-state change, never a rename/retry of the failed shape.

L027: generic Std copy proof had an unreduced Result fmap in the inductive step and used rw under a dependent List.clone match. Corrected own proof to reduce the fmap and use dependency-aware simp. Failed sorryAx diagnostics are not credit.

L028: dependent clone match simplification still left the equality witness. Replaced with explicit match split and returned-value equality in L029, no cap change. L030: extracted-to-cohort port needed explicit from_meta reduction for IAD; corrected L031. L032: shared bracket counter updates needed extensional integer cancellation before reducing Heap fields; corrected L033. L034: validity proof membership and external-guard balance simplification failed; L035 explicitly separates fresh-token and shared/exclusive counters. All failed sorryAx diagnostics excluded.

K033: SDK acquire + fresh allocation under whole-function RefCell/log modifies timed out (98.13s,6,352,292KiB). K034: new typed-guard pre-state bracket contract timed out (98.32s,6,352,032KiB). Neither rerun unchanged. Replacement K035 is a plain native context harness, actual typed SDK guard across allocation, with K036 omitted-drop semantic failure; full modifies remains composed from separately checked callees, not inferred from a plain harness. No full snapshot closure credited.
