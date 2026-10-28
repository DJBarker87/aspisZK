# Execution notes

- Assigned branch already existed at exactly the requested base, with clean
  status; no branch replacement, move, reset or merge was performed.
- Target recount6 files are not present at the candidate base. Read research
  git objects and pin them in input-pins.jsonl; no sibling worktree edits.
- First and second native-upload admission transports exited 255 before any
  compiler or admission script ran. Recorded and retried after >60s. The
  third admission transport exited 0. No submitted compilation was repeated.
- Initial stdlib text checker expected `Ok(...)` inside a match arm whereas
  the actual pinned body wraps the whole match in Ok. Kept initial failure,
  inspected get_creation_mode, corrected the text match and passed --check
  against the unchanged retained source. This was not a compiler attempt.
- The unchanged existing scope/run2/barrier route is reused with job-specific
  paths. The copied job wrapper records SSH 255 and retries only pre-launch
  and read-only commands; a scope submission is never re-submitted on 255.
  No shared launcher, reservation tool or infrastructure source is edited.
- Lean35800 ran once and failed on the reserved field name `exists`; its
  subsequent errors and sorryAx reports are failed-elaboration artifacts,
  not accepted theorems. Rename the field to entryPresent before the next
  assigned attempt. The complete failed output/receipt is retained. Log
  recovery required four read-only SSH retries; no compiler resubmission.
