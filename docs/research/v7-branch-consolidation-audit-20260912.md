# V7 branch consolidation audit — 2026-09-12

## Result

All authoritative local and `origin` branches whose names identify V7 have
already been consolidated into `main` and deleted. No V7 branch ref or V7
linked worktree remains. The active V8 worktrees were not changed.

The audit was performed at:

- `main`: `ab5dced6b29a79a1d5d9c390ca7fbb33d5e9896e`
- `origin/main`: `ab5dced6b29a79a1d5d9c390ca7fbb33d5e9896e`

The working tree's pre-existing untracked research inputs were preserved:

- `.research-inputs/`
- `docs/research/v8-completion-fs-extraction-20260911/`

## Ref audit

The following independent views contained no V7 branch:

1. `git branch --all --no-color`
2. `git for-each-ref refs/heads refs/remotes/origin`
3. `git ls-remote --heads origin`
4. `git worktree list --porcelain`

Only `main` and V8 research branches/worktrees remained. Therefore there was
no live V7 branch left to merge or delete in this pass.

## Consolidation already present on `main`

The repository contains the two broad historical consolidation joins:

- `e2c1ba4b483d8d77bac46cde247832c540bfdcbf` — consolidated V7 branch
  histories, including the K1.2 Merkle source bridge and the Pool, wallet,
  one-terminal, eight-lane, K1.3, K1.5, and Tag-73 implementation lines.
- `c9478ba550fcf68142993cc1e8a67bb265455edc` — consolidated the subsequent
  V7 research histories.

The later September integration chain is also reachable from `main`:

- `fc5c5b8ddff7f3387861e3a811ec43bb0d0d7b39` — September 1 V7
  consolidation, ending with the Registry V2 release audit.
- `c4e557f2c99b8714feb4a38117f284684f7ef38e` — all-reachable CU-bound
  testnet line.
- `b6ba075aec78f8ab871ea5dedc0be1fc2cc83d24` — one-transaction activation
  line.
- `f27d88a2f3ff4b601c7e053b7666233aee8ed87e` — persisted-lane source/formal
  closure.
- `f536082c43a7ad5d1dfdf8da40625768f9d399b4` — persisted-lane integration
  candidate.

## Previously reported branch tips

The previously reported V7 milestones were checked directly. These tips are
ancestors of `main`:

- `bddf1b4c7821b4953b72b3a9c84ecdf4fbbb92c2`
- `366628641b626a16d8afbf2f8a850f78561f08ee`
- `ee6f38fdc4f605fec5e61e48baed3750d1ff99e6`
- `87ec2d5f7f6ce8d3e8a490d60280c5bafe37b7b7`
- `a07dfcff41d40cee854f90ce36213ef9326ac658`
- `76936a4f6b1f572307c32dc61c2c7e18565c789f`
- `32002a3417f3656ba00535710ae7abe3aee26621`
- `69ec6de5fb2cb8f4600dc071dc4ca3e1c7e97bb7`
- `52df136ab84dff3697bae00a431e166ae45ce745`
- `a2db22373dacf323c82b348d0dbe232925506c6c`
- `97e50660d61bfc07fb22bb0a6cc8a268fe073352`

The historical K1.5 replay tip
`c092e52a980e3c2b0e79604b5e3461b277e10cf2` is not an ancestry parent
because that line was replayed by cherry-pick. `git cherry` classifies all six
commits on that line as patch-equivalent to `main`. The corresponding `main`
commits are:

| Historical commit | Patch-equivalent commit on `main` |
| --- | --- |
| `ce7cfefe` | `8a200895` |
| `5ad0b39f` | `30e33b37` |
| `40694479` | `157dfbd2` |
| `75f3ff5c` | `bcbfdb5a` |
| `be3a424d` | `a7ceb1f8` |
| `c092e52a` | `f3de26e9` |

## Deleted-object and stash audit

An unreachable-object scan found historical experiments, superseded commits,
amended commits, and older V5 work. This does not identify a live branch ref.
Of 451 unreachable commits, 330 have a patch-equivalent commit on `main`.
The remaining objects include obsolete seven-lane experiments, abandoned WIP,
amended merges, and older V5 alternatives; importing them would reintroduce
superseded states rather than recover a missing branch.

One V7-labelled stash remains:

`stash@{0}: root-q16-delta-duplicate-before-main-reuse-20260830`

It reduced `V7CompactFrontierDeltaCertificate.lean` from 5,227 lines to a
37-line aggregate. Current `main` supersedes it with a four-line public module
that re-exports the separately factorized `DeltaSum`. The stash was left intact
because the requested deletion scope was branches, not user stashes.

## Final deletion rule

A V7 branch may be deleted only after one of these checks succeeds:

1. its tip is an ancestor of `main`; or
2. every non-merge commit is patch-equivalent to a commit on `main` and any
   intentional conflict resolution is documented.

At the end of this audit the deletion candidate set was empty: prior
consolidation had already deleted every local and remote V7 branch.
