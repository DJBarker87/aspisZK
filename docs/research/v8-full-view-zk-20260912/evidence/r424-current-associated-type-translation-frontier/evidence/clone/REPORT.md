# R424 pinned OCaml/Dune build preflight

Scope: read-only inventory for a future isolated R424 Aeneas candidate. No workspace was copied, no source/cache file was changed, and no build or test executable was launched. This report does not choose the source transformation or claim it preserves semantics.

## Pinned workspace and build evidence

The reusable source/cache workspace is `/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a/src`, based on the R385 v2 receipt at `.r21-scratch/r385-private-return-carrier/build-evidence/v2-a962b9ac222c-20261002T153548Z/`. The pinned container image is `sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7`. A small read-only Docker invocation (network disabled, 1 GiB memory/swap, 16 pids, source mounted `:ro`) observed opam switch `5.2`, OCaml/opam compiler `5.2.1`, Dune `3.24.2`, and these relevant installed packages:

- `core v0.17.2`, `core_unix v0.17.1`, `ocamlgraph 2.2.0`
- `domainslib 0.5.2`, `progress 0.5.0`
- `ppx_deriving_yojson 3.9.1`, `ppxlib 0.35.0`, `visitors 20250212`, `yojson 3.0.0`
- `charon` is installed and `ocamlfind query charon` resolves to `/home/opam/.opam/5.2/lib/charon`.

Workspace/config hashes observed on that candidate:

- `src/dune`: `1810e39742dcf46f3e2e9b5afd327b1b1bab05894b82e33fb2fe40524348f5e5`
- `src/dune-project`: `dc9617fb4b5f04efed96ef3c0e2fa15eab5c72cfb2e4bf807a72afdff09494af`
- `src/aeneas.opam`: `47bb3fff39b2641c9a3d8eae23bb64539357c64f1a0b7fb985c2a4b6dbe01a19`
- `src/aeneas.ppx.opam`: `479c060fd275c2ab7cdab3f419845a9bf6bb94bc3b9e88f3f7a189f48cf56881`

The root Dune file defines one `aeneas` library and the `main.exe` executable; it has no test stanza, test directory, or test executable. The library includes `RegionsHierarchy`, `InterpUtils`, `Substitute`, `TypesUtils`, and `PrePasses`; its dependencies include `charon`, `core_unix`, `ocamlgraph`, `str`, `progress`, `domainslib`, and `ppx_deriving_yojson`, with the listed PPX preprocessors. Dune language is 3.7. Both `dev` and `release` flags are explicitly configured; R385 invoked the `release` profile and a static native link for `main.exe`.

The warmed cache contains `_build/default/aeneas.cmxa` (539,190 bytes), `_build/default/main.exe` (49,453,432 bytes), and byte/native outputs for `aeneas__RegionsHierarchy` including `.cmi` (6,634 bytes), `.cmo` (50,267 bytes), `.cmt` (90,902 bytes), `.cmx` (6,876 bytes), and `.o` (82,760 bytes). The cache was touched by failed R385 v1 before successful v2. The successful receipt explicitly does not claim other `_build` entries byte-identical to pristine R363; only the pre-v2 `main.exe` hash matched R363. R385 v2 built `main.exe` successfully in 6.69s, GNU-time max RSS 502,864 KiB, container cgroup sampled peak 564,842,496 bytes, swap peak 0; output executable SHA256 `f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5`.

## Safe candidate recipe evidence

The R385 preparation script `.r21-scratch/r385-private-return-carrier/prepare_clone_remote.py` used `shutil.copytree(..., symlinks=True, copy_function=shutil.copy2)` from the separate R363 candidate into a previously absent destination. It scanned the full tree before/after, compared file content/mode/type and symlink targets, and rejected any shared regular-file inode. Its result recorded one source symlink and zero shared regular-file inodes. The corresponding source was not modified by the copy operation.

For a new R424 candidate, the mechanically supported starting point is therefore: use a fresh absent destination; ordinary-copy the selected pinned R385 candidate (including its warmed `_build`, preserving symlinks); compare pre-copy and post-copy tree manifests; assert zero shared regular-file inodes; retain the source cache as the parent and never build in or patch it. Before build, record source/config hashes and cached artifacts. Any separate candidate build should use a unique systemd scope and Docker container name, not the existing `aspisr385.slice` or R385 destination.

R385's successful capped route was:

- systemd: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`;
- Docker: pinned image above, `--network none`, `--memory-reservation=5g`, `--memory=7g`, `--memory-swap=7g` (equal to memory, so no container swap), `--pids-limit=128`;
- one Dune/opam job (`OPAMJOBS=1`, `DUNEJOBS=1`, `dune -j 1`);
- host reservation check required at least 24 GiB `MemAvailable`, and recorded running user services and Docker containers before launch.

These are the observed R385 settings, not authorization to run an R424 build. A future runner must use a fresh cgroup/container name and recheck host reservations/current concurrent `MemoryMax` before any launch.

## Smallest useful typed target / test route

There is no pre-existing test target. The smallest reusable compiled unit for a changed `RegionsHierarchy.ml`-level implementation is the corresponding byte/native object in the `aeneas` library, rather than linking all of `main.exe`. Candidate Dune target spellings to validate in a writable isolated copy are `_build/default/.aeneas.objs/byte/aeneas__RegionsHierarchy.cmo` and `_build/default/.aeneas.objs/native/aeneas__RegionsHierarchy.cmx`; the cached artifacts establish these object paths exist, but this inventory did not prove Dune accepts either as a direct target argument.

For a typed behavior check that calls an exported function, a minimal dedicated executable stanza/module linked against `aeneas` can be added only in the fresh candidate. That route would typecheck the public call site and execute a narrow fixture without making `main.exe` the first diagnostic target. Since the library has no test stanza and the tested declarations/visibility are not yet selected, the exact fixture/stanza remains for the lead to specify after source review. Do not add it to R385.

## Probe boundaries and retained failures

- `dune describe targets --format=plain` is unsupported by Dune 3.24.2 (`--format` unknown); no build was run.
- Retrying `dune describe targets` on a Docker `:ro` mount failed because Dune tried to open `_build/.lock`. No cache mutation occurred because the mount was read-only. Therefore no target list is claimed from that probe.
- A container package-filter probe used `rg`, which is absent in the image; it was corrected with `grep` to collect the package versions above. No workspace/cache mutation occurred.

## Sources

Primary local records are `provenance/R385-v2-build-plan.json`, `provenance/R385-v2-run_cached_build.py`, `provenance/R385-v2-launch_build.py`, `prepare_clone_remote.py`, and the v2 `build-command.json`, `build-result.json`, `compiler-gnu-time.txt`, `docker-inspect.json`, and before/after reservation records. All paths are relative to `.r21-scratch/r385-private-return-carrier/` unless noted above. This preflight is environmental/build evidence only; it contains no Aeneas source repair, translation, Lean result, or semantic conclusion.
