# Stage 1: prefix-only producer repair

Initial research tip 974db87027 has no KSA_ file or merged KSA_ fix. Read-only
`git ls-tree research` checked this before copying. No other worktree was read.

The LPs L098 import blocker expands to three groups of root declarations:
TypesExternal's Windows and transparent aliases, FieldExternal's field shims,
and FunsExternal's std shims/leaf definitions. L014 retained the next collision
at aspis_core.field.P. LPt_transform.py copies their required 37-module producer
closure by simultaneous module/declaration-name substitutions only. Copied
proof terms, predicates, branches, values and library imports are unchanged;
all renamed symbols are explicitly listed in LPt_COPY_PLAN.json. Both source
and copy hashes are recorded; --check byte-compares every generated copy.
No original module/object or imported library is edited. These are nominal
copies of inherited proofs, not new arithmetic or native verification.

Own serial transport/validation scripts are copied from LPs and adapted only
for this prefix/workspace and the 100-attempt limit. Backend launcher text
remains identical. The own driver paused before admission after L012 so the
root-name transform could be completed; no proof process was killed. L013 and
later copies changed only names/dependencies; no timeout or memory failure.

Persistent designated leaf cache recorded at start: 106 files. LPt outputs
use this same cache; it is retained. No second cache created. Aeneas resolved
objects are pinned by LPt_LIBRARY_START and per-attempt library pins. One
scope per job, reservation exit0 AND allowed:true, 6G/8G/swap0/tasks64, -M7000.
No Kani, Rust, shipped source, cfg harness, lock, feature, wire or ELF change.
Retained release hashes and approved trust/game/headline remain unchanged.

Stage accepted: L017 co-import succeeds; L001–L044 complete the37 copied
producer modules (43 passes, one retained L014 import rejection). Final source
hashes match the latest successful receipts. All printed accepted axioms are
standard. LPt_ByteDomain and LPt_PreparedClaim are the next uncompiled stage.
