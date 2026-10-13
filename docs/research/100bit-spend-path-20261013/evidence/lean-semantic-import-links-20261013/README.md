# Semantic import cache links

The pinned semantic runner first reported that `R0C.CircleRows.olean` was
missing. That absent object and its exact canonical source were linked from
the pinned `aspis-fs-generic-20261006` cache. Its direct imports are
`R0C.SemStatement`, `R0C.Counting`, and `AspisFormal.CircleGroupCardinality`;
all three dependency objects were already present in the runner.

The next retry identified `AspisV8R19.SamplerCirclePolicy.olean` as absent. To
avoid repeated one-module misses, all absent direct `AspisV8R19` objects were
linked in one absent-only overlay. Root order was `objects2` then `objects` in
the pinned generic cache. The run found 1,805 candidate modules, added 1,766
links, and preserved 39 pre-existing files or links. The remote manifest records
every new link's exact target, SHA-256, size, and any sidecars; it is archived
here as `AspisV8R19-overlay-20261013.json`. Cached object bytes were not copied
to the repository.

`R0P-CircleSampler-staged.lean` is a read-only snapshot of the root-staged
source used for import inspection (SHA-256
`00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100`). Its
three imports are `R0P.SemD2`, `R0C.CircleRows`, and
`AspisV8R19.SamplerCirclePolicy`. The root's qualifier-only tower-source edit
left those imports unchanged. `CircleSampler-import-closure.json` gives the
recursive 258-module graph and each available canonical research source path
and hash. `CircleSampler-R19-objects.json` records runner object targets and
hashes for the 36 R19 modules in that graph; all are present.

The exact local canonical source for `SamplerCirclePolicy` has SHA-256
`2aeaf83e87e04f4cd9cda722a5c0f9e8ae0f85f24e12e2edb359cdee7cf73f7b`, matching
the existing R729 direct-import pin. It imports `SamplerFieldDecode`; its
recursive import graph is captured in the module closure JSON. No Lean build or
theorem-source edit was performed for this task. Root owns the dependent retry.
