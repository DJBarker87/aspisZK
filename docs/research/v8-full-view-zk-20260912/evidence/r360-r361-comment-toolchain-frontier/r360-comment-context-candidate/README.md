# R360 instantiated-name comment candidate — prepared, unbuilt

This is a fresh isolated copy of the built R349 source/cache tree. It is not based on the failed R356 candidate. The sole source edit is the lead-specified `extract_comment_with_span` case for names containing `Types.PeInstantiated`; it displays `name_to_string ctx name` under `Instantiated source name`. The call uses this module’s local `name_to_string` API: R349 `ExtractBase.ml` line 634 takes an `extraction_ctx`, and existing `ExtractTypes.ml` calls pass `ctx` at lines 833, 845, and 905. The exact declaration/call excerpts and full-file hash are saved in `name_to_string-context-excerpts.txt` and the audit.

The original comment branches remain verbatim, as do the pattern-name helper calls, `extract_attributes`, all logical matching code, source metadata, and every other source file. Exact reconstruction confirms the full R360 `ExtractTypes.ml` differs from R349 only by the inserted case. The recursive clone audit compares against the fresh R349 source/cache copy: 1004 entries, the one authorized source-path difference, zero shared regular-file inodes, and identical cached R349 executable bytes.

The saved R349 pre-build source tree manifest predates the R349 native rebuild and therefore differs under `_build`. The audit verifies its non-build source entries, then compares the complete live R349 source/cache tree to the R360 clone directly; all cached build-tree entries match. The previous R356 failure remains in its own evidence bundle and is not altered here.

Preparation only: no build, translation, or Lean compilation was run.
