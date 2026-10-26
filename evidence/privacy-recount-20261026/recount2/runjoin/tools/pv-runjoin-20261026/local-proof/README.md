Focused checks only, using `lake env lean -M7000`. No dependency is built.
The local package is empty; LEAN_PATH supplies the existing mathlib cache and
read-only copies of the shared J objects/Aeneas backend .olean/.ir artifacts.
Local/host Lean githash:8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Both mathlib roots are81a5d257c8e410db227a6665ed08f64fea08e997.
No Linux native libraries are imported. Each new proof is checked by the local
Lean kernel. This is a focused cached check, not a frozen release replay.

20981 initially lacked same-namespace imports in the first LEAN_PATH root;
20982 then exposed missing serialized IR cache artifacts. No declarations
were checked in either input rejection. Existing .ir files were copied; no
backend, launcher, toolchain, cap or monitoring infrastructure was changed.
20984 passed after that cache completion and a source proof change replacing
broad simp by List.length_ofFn. Local files under .lake/objects/cache directories
are ignored and never committed. 20985 emits the previously absent FiniteGraph
object required by the new CompletedWorld consumer; it is not a full rerun.

The two graph marginal laws are mathematical identities. Native E1/effect
association of the initializer remains a named obligation, not a consequence
of finiteness. Full native proof audit objects are retained by UnifiedRetry.
