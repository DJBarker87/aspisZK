# Actual selection investigation (entry 0ec90874e3)

Target not yet established. No selected Input has been constructed or replaced.

`PV_RunJoin_InstalledFamily.Selection.selected` is a data field, taking the honest prover, statement and witness. `InstalledEndpoint.runtime`, `JoinedFamily.inputs` and `FixtureSelectedSources.both_source` take that selection as an argument. `SourceSelectionContract.selectedRecord` simply applies the supplied field. `EndpointSelection.selection` extends a supplied endpoint selector; it does not supply one. `EndpointSelection.data` additionally requires the endpoint binding as a hypothesis.

The frozen source `crates/aspis-r1-cost-probe/src/RealR1_client.rs:20` takes public and compiled arguments; it neither compiles nor selects their operational arguments. Its tests at `RealR1_client_tests.rs:7,28` use `r0_fixture::prepare(withdrawal)`. The fixture generator compiles the native arguments, but no equation currently identifies a deployment installation of `Selection.selected` with that result. Fixture literal metadata is not used to assert that equation. A request for the concrete installation artifact is pending; independent native canonical-public proof work continues.

Needed, without changing i: request, witness, change, laneAnchor, snapshot associations, followed by the compiled-payload association, for the actual deployed selector. `SelectedPackage20` then supplies compiler return, full transition, recorded public input and admitted trace at that same i.

Rows removed so far: none. V038, V045, V047, V152–V154 retained. Recount 5 says “Deployed P remains OPEN, record counts 2/8/6 unchanged” and “Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.” This investigation changes neither statement. Endpoint premise removals/additions/weakenings 0/0/0; constructed P {source public binding, trace} unchanged; deployed P OPEN→OPEN. Recount 5: 407 rows, 400 P, 3 T, 4 C; OPEN 93. T remains exactly entropy_law, entropy_kernel, observation.
