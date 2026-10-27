# Active fourth-pass state

User task: use all 100 charged Lean attempts + 4 small-width/control Kani runs;
Env-J 52400–52699, last 52697–52699 reserved audits. Never reuse IDs. New tally
`evidence/pv-cblib-20261027/TALLY-resume9.json`; inspect it, do not reset it.
The shared rulings and restored flag were read. No local Lean, SHA-NI work,
production source edits, trust-field changes, pushes or other-worktree edits.

Committed stages after base 4aaa5ae9a2: 1d69d6fa84 padding content;
fe115cb0c6 byte decoder + soft compression; 2672254f44 owned finalization.
Rows still 7. Full fixed owned finalizer content/totality, all 32 digest bytes,
byte-block fold, default/constructor, buffer transition/eager/totality now pass.
Buffer content fold and deterministic complete one-shot model are pending.
All accepted axioms standard, peak <2.7M KiB, swaps 0. Exact numbered receipts.
`resume9-summary.py` produces RESUME9-RECEIPTS.json.

Currently running local tool session 90502: `resume9_queue.py` starts at
DigestUpdateModel, then DigestUpdateSource, DigestSoftTotal, PadArrayModel,
PadArraySource, FinalizeSoftSource, DigestSoftSource (earlier queued targets
already passed; never restart them). It is repeatedly admission-refused,
using fresh IDs and 3+ minute waits; scanner sometimes sees >55 GiB before
our scope. Do not run another capped scope concurrently. `ps` identifies the
local parent; it is permitted to terminate only this own waiting queue for a
reasoned reprioritization, never a remote/shared process. No change to caps,
launcher, resource scanner or quiet marker. Next target is still smallest-first.

Tools: resume9_lean.py calls standing resume_lean.py/receipt collector;
resume9_queue.py honors refusals and current tally; max 100, 97+ audit-only.
New sources in docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CBL_*.
Some extra untracked draft Lean files are optional; do not claim or import
uncompiled drafts. Preserve failed snapshots as evidence; move unneeded drafts
into evidence at end if not compiled. Standard generators have --check.

Own host /home/dombarker/project-offloads/codex-pv-cblib-20261027, SSH
 dombarker@100.108.41.90. Source-proof/lib.rs is verified hash
210425a9c8a4e507b3a4c453a1226f6979580ba04534b2dd7a18e5f4bf4860c0.
Owned final + full buffer driver extracted successfully. Raw outputs in evidence;
resume9-port.py reuses 40/44 exact helpers (only recorded namespace/comment/
whitespace ports). PV_CBL_FinalSoft and PV_CBL_DigestSoft are checked. Do not
reextract unchanged. No foreign template or stub installed.

NEXT after soft focused targets: run four Kani links, all still unspent, through
`resume9-kani-queue.py upload`, then each of `load_be4`, `store_be4`,
`join_resize_two`, `pop_resize_u8` (inspect each result; no unchanged retries of
charged failures). The script invokes resume9_kani.py, charges TALLY-resume9,
uses 180s, taskset0-3, opt3, caps6/8/swap0/tasks64; unique rNN admission labels.
No array or old timed-out pop gate rerun. First two are SHA byte codec links.
Native harness/reference body equality check: resume9-reference-check.py.

Then std extraction (no new source upload required; these funcs are in verified
lib): `queue_extract.py join-resize-opt resume9-std`, `pop-resize-opt`,
`array-slice-result-opt`. They use supported resize instead of foreign clear /
remove; array returns full Result using Slice.to_vec on Err. Check for foreign
external templates; never invent a leaf. Extracted generic Array kernel already
proved in old modules. op32 allocator-effect deferral untouched.

Aim for op26 candidate law via byte reference + checked String encode/decode
adapter (StringBytesAdapter existing); native join lengths0–2 every coordinate.
Publish additions through namespace R1Z.PV_CBL_CallbackBundle in a NEW module,
importing old AppendBundle to retain all 7 existing names. Avoid a cycle by
editing/importing AppendBundle from old CallbackBundle itself. Stable names add,
never rename. Reopen namespace in PV_CBL_CallbackPublication / equivalent.
Pop Copy actual payload Result<Word,Error> is Copy (frozen source checked), but
new u8 bounded link is not the old large-payload association; keep that explicit.
Array N=1024 native success/owned association remains open absent proper evidence.
No SHA V231–V238 row credit merely for owned reference; native wrapper loans /
Drop / dispatcher / deployed association still open. Canonical endpoint removed0.

Reserve at least 3 attempts for 52697–52699 final CallbackAudit, SelectionAudit,
one own Manifest replay. Generate/check manifest after focused targets green;
#print axioms all new top theorems, standard only. Do not repeat full regression.
Commit path-limited every2–3ops/stage, no attribution, no push. Final report <500
words: rows7→?, exact soft status, receipts target/exit/wall/RSS/swap/revision/
axioms, commits, premises0 removed / T unchanged, next deliverable, target not
established. User mandates no early stop while compile budget remains except
checked ROW counterexample; report counterexample without fixing ROW.
