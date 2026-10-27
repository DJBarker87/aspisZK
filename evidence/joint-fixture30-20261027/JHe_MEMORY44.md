# Attempt44 replacement

JHe_NativeAssociation.source at044 was rejected by Lean's -M7000 kernel
memory limit (7170456 KiB peak RSS; swap0), after concrete record restoration
with a local actual dictionary let and field rewriting. The source also
contained an already-closed-goal error. No credit is assigned to its printed
recovery audit (which mentions source).

Replacement: isolate the record-update implication in JHe_WriterRestore,
quantified over two arbitrary Ops records. Apply that checked theorem to the
already checked JHe_CurrentAssociation.source and the original-writer slot.
The new concrete proof is one named theorem application. This is a changed
proof shape, not an unchanged retry or a larger-cap run.

Attempt47's combined fixture+IDa security closure was rejected at the
interpreter (-M7000, exit134, peak7196428KiB, swap0). It was not rerun unchanged.
Replacement: JHe_InstalledData is definition-only fission of IDa's six data
constructors (Uninstalled,finish,boundaries,seed,deployedConfiguration), with
no security theorem. JHe_HeadlineConfiguration separately checks equality to
the actual IDa source. Only own-prefix modules and their dependent objects
are rebuilt; the shared imported cohorts and host infrastructure are unchanged.

057 confirmed that definition-only import fission alone was insufficient
(exit134/7174040KiB/swap0). The next split checks the concrete original-writer
candidate in JHe_OriginalSelected without configuration imports, then uses
JHe_TransportCall's generic equality eliminations. The final DeployedChild
is a direct named application with all arguments explicit, with no concrete
record rewrite tactic or generic-candidate instantiation in that interpreter.

060's direct transport application still exceeded the import/interpreter
limit (exit134/7173512KiB/swap0). The unconditional combined SDK root is now
archived as text only. The permitted alternative is an explicit453-equation
SHA-realization hypothesis for the first batch, with no acceptance field.
061's flat453-field record exceeded -M7000 during elaboration; it was replaced
by three smaller records and a three-field aggregate. 062/063 expose aliased
request names; 064 rejects an import-order generator error. 063 was an
accidental unchanged ordinary-error rerun after a failed generator preflight;
no extra evidence credit is claimed. Generator preflight now validates import
ordering and a failing check prevents its dependent compile batch.
