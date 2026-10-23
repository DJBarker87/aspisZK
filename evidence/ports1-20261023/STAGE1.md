# Stage 1 — library operations

Claim: `Port1_Library.library_join` supplies the exact library field of
`VTop_OracleStages.ConeJoins` for `implementation ops sourceBody` and
`implementation (std ops) modelBody`, conditional only on the named
`TrustedStd ops`. It preserves complete dependent Result values, including
fail/diverge, and gives an empty oracle log. `library_no_read` is total;
`release_mark` is exactly observer None, empty log, and ok unit. The thirteen
nonlibrary body operations retain their supplied oracle programs.

Concrete source helpers: `Port1_LibrarySource` contains the identifier-relocated
retained unrolled decoder, ZERO, mark, Option::ok_or, Result::unwrap32.
`Port1_LibraryDecode.decoder_agreement` proves symbolic carrier transport to
the retained parser; `strict_fixed` and `wrong_length` reuse its strict decoder
refinement. All eight limb guards remain. No sampler/reducing decode is used.
Constants op14/15/16/20/21/22/23 are respectively
7783/7751/10/10055/8007/7527/7495. `Port1_audit.py` checks their source equations,
compares both Rust decoder bodies with the retained extraction's source, and
checks identifier-only Lean body relocation. Full source pins are in manifest.

New explicit TrustedStd fields (D157 and the existing D133/D145 library policy):

* `option_ok_or`: Option::ok_or at candidate.tx2_common's inactive strict decode.
* `result_unwrap32`: Result::unwrap after the checked folded-root slice-to-array
  conversion in candidate.tx1 and candidate.tx2_common; Err maps to panic.

Existing Aeneas std slice/array/number semantics and source extraction trust
are reused. No library trust field states stage acceptance, outputs, log or
model identity. `std_semantics` exhibits an inhabitant; it does not prove the
fields for an arbitrary pre-existing dictionary. `install` pins nonstd helpers;
this is an explicit installed interpretation, not equality for an unbound Ops.
No SDK/interior-mutability trust extension is made.

Validation: 5 actual focused Lean attempts (IDs 001,003–006), 3 final modules
accepted. ID002 failed dependency preflight without launching Lean. IDs004/005
had elaboration errors; historical recovery sorryAx lines are excluded.
Final strict decoder: lean006 exit0, standard axioms only. All receipts include
exact command/target, source revision+hash, dependency object fingerprints,
wall/RSS/swap, cgroup limits and full axiom lines. Every compile ran on the
host with the shared global Lean lock, one thread, -M4400 and 6G high/8G max/
swap0/64-task cap. No overlapping Lean was observed at admission; no timeout,
memory kill, cap increase, Kani or Rust job. Parser cache was copied read-only
from the pinned local gather cache into this worker's private host directory;
existing host objects were not overwritten. This is focused reuse, not a
coherent release replay.

Port-table row closed: **library**, for this explicitly installed source/model
interpretation and the listed std fields. The source verifier must use this
interpretation; no assertion about an arbitrary headline rust is established.
All other body/source/runtime/annotation obligations remain as listed.
Shipped files and ELFs are untouched; the rebuild trigger did not fire.
