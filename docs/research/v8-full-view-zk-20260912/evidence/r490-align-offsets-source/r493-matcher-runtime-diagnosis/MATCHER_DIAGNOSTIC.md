# R493 focused matcher diagnosis

The R493 built-in alias was compiled into both the Dune-generated source and candidate binary, but the alias does not classify the selected captured function. The failure is in the pattern's generic-variable match, not stale generated code.

## Exact selected input

The probe loaded pinned R490 input `R490LiteralInitializerCandidate.llbc` (SHA256 `a3295333237b0dfad164b826a6d8ce6b2d183d177ca1453489e0e1d2a74a2698`) and selected `FunDeclId 1`. Aeneas/Charon rendered its source name as:

`core::slice::{[u8]}::len<u8>`

The R493 candidate source and generated Dune source both have SHA256 `7963be0b32879555b88960d61d5593780261f82950d06054437cbdb144a5bd16`. The R493 candidate executable has SHA256 `c8562f6354832214639c5325ca0cc586ada9671189395c19a6fd6f37a7bdabee`.

## Focused runtime results

The harness called the pinned matcher implementation's direct `match_name_with_generics`, built one-pattern `NameMatcherMap.find_opt`/`find_with_generics_opt`, and the actual `ExtractBuiltin.builtin_funs_map ()` lookup against Fun1.

| Pattern | Direct match | One-pattern map lookup |
| --- | --- | --- |
| `core::slice::{[@T]}::len` | no match | no match |
| `core::slice::{[@T]}::len<@T>` | no match | no match |
| `core::slice::{[@T]}::len<u8>` | no match | no match |
| `core::slice::{[u8]}::len<@T>` | no match | no match |
| `core::slice::{[@T]}::len<@U>` | no match | no match |
| `core::slice::{[@T]}::len<@>` | no match | no match |
| `core::slice::{[u8]}::len<u8>` | match | match |

The actual R493 `builtin_funs_map` returned no match for Fun1 using both `find_opt` and `find_with_generics_opt` with empty explicit generic arguments. The concrete pattern proves the installed map path can classify the selected `Fun1` when given its exact source instantiation.

## Why the generic alias fails

The pinned Aeneas `ExtractName.ml` sets the name-match configuration's `map_vars_to_vars = true`; `NameMatcherMap.find_opt` uses that configuration. In pinned Charon `NameMatcher.ml` at `update_tmap` (around line 357), `is_var` is true only for `TVar _`, and the function returns false when `map_vars_to_vars && not is_var`. Fun1's suffix supplies concrete type `u8`, so `@T` cannot match that concrete type in either the slice impl pattern or the terminal `len` generic argument. Concrete `u8` matches both positions.

The smallest route verified by this focused probe is an exact registration `core::slice::{[u8]}::len<u8>` mapped to the already existing `Slice.len` target with the existing `can_fail:false` and `lift:false` options. This conclusion is limited to the selected concrete instantiation; it does not establish a general mapping for other slice element types.

## Build and runtime evidence

- Probe source: `MatcherProbe.ml` in the adjacent scratch directory.
- Actual LLBC SHA256: `a3295333237b0dfad164b826a6d8ce6b2d183d177ca1453489e0e1d2a74a2698`.
- Pinned Charon matcher source SHA256: `a6aac1d07e356b864a9146723e31401ff26be569ce2ac71d7410bc14d1bb5061`.
- Candidate and generated mapping source SHA256: `7963be0b32879555b88960d61d5593780261f82950d06054437cbdb144a5bd16`.
- Candidate binary SHA256: `c8562f6354832214639c5325ca0cc586ada9671189395c19a6fd6f37a7bdabee`.
- Target: cached Dune `matcher_probe.exe`, release profile, `-j 1`, followed by a runtime matcher query on Fun1.
- Probe exit status: 0. GNU time for the focused Dune target: 1.16 seconds, maximum RSS 236064 KiB, swap events 0. Outer systemd scope: MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128; Docker used the pinned image with a 7G memory/no-swap cap.
- Complete matcher output and timing: `evidence/matcher-runtime/variants.log` and `evidence/matcher-runtime/variants-time.txt`.
