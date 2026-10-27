# XRi route C prime association continuation

Adopted top: AspisR1.ARX_Root.deployed. Target not yet established.
Current-round limits: 100 Lean attempts, 10 Kani runs, zero extraction invocations.
Only XRi-prefixed artifacts in this evidence directory are changed. No shipped
source, ledger, contract, main LEAN_PATH or session A worktree is modified.
Host workspace: /home/dombarker/project-offloads/codex-cx-extraction-assoc1-20261027.
Library/cohort reuse: coherent sound-int2 workspace, first workspace root then
objects, preceded only by the new XRi_objects directory. Generated namespace
XRh_Release is already isolated from the cohort and is preserved byte for byte;
no namespace rewrite or extraction invocation is made.

## Stage 1: external implementation blocker

XRi_L001 was an admitted preflight, NOT a Lean compile. The unchanged coherent
S2W_lean_host.py refused XRh_Release.TypesExternal (FileNotFoundError) before
calling its command runner. No compiler receipt exists. XRi_L001.json gives the
intended exact target, command, revision and path order; barrier and preflight
logs are retained. Exit 1. Lean wall/RSS/swap and #print axioms: N/A, compiler
not invoked. No timeout, memory kill, cap change or retry. One capped scope,
6G/8G/swap0/tasks64; no concurrent own scope.

Types.lean imports XRh_Release.TypesExternal. Emission contains ONLY
TypesExternal_Template.lean, declaring axiom Windows, axiom WideExact and axiom
FibreIndex. Funs.lean likewise imports XRh_Release.FunsExternal, supplied only
as an axiom template. Those are not pinned Aeneas library modules. Installing
the templates would introduce nonstandard axioms; substituting the cohort's
carriers/functions without proof would assume the association being requested.
No such substitution is installed. Raw output snapshots have XRi_ names and
.lean.txt suffixes; their contents and hashes are unchanged.

Every generated declaration's elaboration status is BLOCKED/NOT TESTED behind
this missing external dependency, not FAILED mathematical elaboration. No
specific generated declaration error is inferred from the preflight. No
mechanical generated fix is made; neither generated file is retried. Full
elaboration requires real external implementations and correspondence first.
The empty generated failure list means no compiler ran, not that code passed.

The launcher behaved as designed. No infrastructure is repaired or bypassed.

## First compiler invocation (XRi_L002)

After all Kani scopes ended, the unchanged S2W command runner invoked Lean
directly once, with pinned Aeneas object hash and raw source bytes, to retain
the exact import diagnostic. This is the first compile, not an unchanged
compiler retry or a repaired/bypassed admission barrier. Exit1, wall
0.271323047s, peak RSS865856KiB, swap0. Missing object
XRi_objects/XRh_Release/TypesExternal.olean; source Types.lean:3:0.
No declaration elaborated and no theorem/#print axioms result exists.
Funs is blocked transitively and not pointlessly invoked. No generator edit,
external-template adoption, library replacement or launcher source change.
