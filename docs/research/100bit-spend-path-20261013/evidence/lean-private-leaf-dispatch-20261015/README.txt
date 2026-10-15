Focused PrivateLeafDispatch check, 2026-10-15

Input graph module was integrated at6a4a73bee from worker32d130241.
The first check failed due to one extra binder in the snoc induction case;
that failed source and log are retained. The generator was corrected and
rerun, keeping all graph edges and theorem statements unchanged.

Corrected module: exit0, wall3.965s, sampled process-group peak1277952KiB,
process swaps0. All3axiom reports are [propext,Quot.sound], without sorryAx.
The first failed elaboration's sorryAx reports are not accepted evidence.
Local lake env lean uses Lean4.32.0-rc1, -M6000 and7GiB process-group stop;
no host, package replay or cold dependency build. The module imports Std only;
the retained merge overlay is on the search path but no local module is imported.
Exact commands, sourceSHA and checkout revision are in the receipts.

The theorem bounds one designated dispatch in the extracted graph. It does
not prove Rust/importer preservation, callback SHA effects, runtime failure
preservation, or the full verifier call count. Those remain OPEN.
