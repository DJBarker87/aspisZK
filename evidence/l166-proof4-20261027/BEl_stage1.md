# Reference source stage

BEl_rust is a standalone proof-only crate. No release file or module inclusion
has changed. BEl_generate.py --check checks copied function bytes and records
all import/visibility/constant/error-carrier substitutions. The verifier prefix
and all batch helpers remain actual bodies; there are no Kani stubs/contracts.

The owned safe reference keeps shared idx/val across all three calls; every
? retains the already written recorder prefix. Recording pushes an attempt
before backend entry and fills its returned Result only after return. Part
boundaries and concatenated oracle address are both retained. A nonreturning
backend leaves None, not a fabricated returned failure. The recorder itself
allocates: allocation failure/abort erasure is an additional lowering issue,
not silently covered by a successful host run.

The first local tests quantify over all832 opening bytes and any returned
32-byte digest, one call per leaf. The whole_batch probe uses arbitrary proof,
queries, roots and both ordinals but a CONSTANT reply backend: even if green,
it does not establish arbitrary adaptive reply semantics. An explicit generic
backend simulation or arbitrary reply tape is required before whole-body credit.
No physical or top-level premise removal is claimed at this stage.
