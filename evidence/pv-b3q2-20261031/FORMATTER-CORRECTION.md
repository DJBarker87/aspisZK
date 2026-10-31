# Formatter correction and quarantine

The former “actual Formatter axiom” interpretation is superseded. The read-only
report on `codex/pv-fmtaudit-20261029` establishes that all inspected cohorts load
Formatter as def Unit in the formatter-repair source profile (SHA-256
`daeafff88224be0870aadb6c3bad73ae7c9375c2de9bbceb177ed2d183d6bdc5`). The
reported dependency of the retained numeric formatter is stale export-time
axiom metadata. It is not an actual axiom declaration or an inconsistency.

The semantic mismatch remains: Rust formatting propagates a rejecting writer's
error, whereas the Unit/always-Ok model does not. No result here uses that model
as a source law. No String/infallible-writer certificate or faithful writer model
is supplied. The route is fmt-1(a), with local source-guard prerequisites only.
The complete endpoint source/event unreachability certificate remains open.

The two historical actual-function diagnostics
`PV_B3Q_FormatCounterexample.rejecting_instance_false` and `concrete_rejection`
remain quarantined. No formatter library consumer cohort was rebuilt, and no
quarantine is lifted on the strength of a stale list or a fresh renamed port.
The prior literal-port refutation stays at its original diagnostic scope; it
is not an op227 counterexample or a std catalogue closure.
