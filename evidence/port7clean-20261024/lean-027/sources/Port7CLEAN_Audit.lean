import Port7CLEAN_Accepted
import Port7CLEAN_Driver
import Port7CLEAN_TraceObstruction

-- One final focused audit; no full frozen manifest replay.
#print axioms AspisR1.Port7CLEAN_Terminal.typed_of_finish
#print axioms AspisR1.Port7CLEAN_Recovered.of_typed
#print axioms AspisR1.Port7CLEAN_Carrier.erased_statement
#print axioms AspisR1.Port7CLEAN_Carrier.reached_statement
#print axioms AspisR1.Port7CLEAN_Carrier.checks_to_source
#print axioms AspisR1.Port7CLEAN_Carrier.transcript_statement
#print axioms AspisR1.Port7CLEAN_Carrier.parsed_valid
#print axioms AspisR1.Port7CLEAN_Carrier.canon_parsed
#print axioms AspisR1.Port7CLEAN_Carrier.first_proof
#print axioms AspisR1.Port7CLEAN_Carrier.rows
#print axioms AspisR1.Port7CLEAN_Extractor.fixed
#print axioms AspisR1.Port7CLEAN_Accepted.terminal_from_calls
#print axioms AspisR1.Port7CLEAN_Driver.accepted_entry
#print axioms AspisR1.Port7CLEAN_Driver.first_accepted
#print axioms AspisR1.Port7CLEAN_Driver.accepted_stages
#print axioms AspisR1.Port7CLEAN_TraceObstruction.interpret_empty
#print axioms AspisR1.Port7CLEAN_TraceObstruction.stages_empty
#print axioms AspisR1.Port7CLEAN_TraceObstruction.driver_empty
#print axioms AspisR1.Port7CLEAN_TraceObstruction.no_sampler_embedding
#check @AspisR1.Port7CLEAN_Accepted.terminal_from_calls
#check @AspisR1.Port7CLEAN_Extractor.fixed
#check @AspisR1.Port7CLEAN_Driver.accepted_stages
#check @AspisR1.Port7CLEAN_Driver.accepted_entry
#check @AspisR1.Port7CLEAN_Driver.first_accepted
#check @AspisR1.Port7CLEAN_TraceObstruction.no_sampler_embedding
#print AspisR1.RawRecordedOracleExtractionMassBin.CleanAcceptedModel
#print AspisR1.Port6AUTH_Prefix.source
#print AspisR1.Port6AUTH_Prefix.bad
#print AspisR1.LiteralAcceptanceTerminal.Checks
#print AspisR1.Port4D_Pairing.PairingLaws
#print AspisR1.Port4D_Pairing.RoundLaws
#print AspisR1.R3SemanticRemainingJoins.EquationEndpoint
#print AspisR1.Port5Q1_QueryPorts.SessionAPrepare
#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives
#print AspisR1.CheckpointBytes4SavedFields.BodyMatches
#print AspisR1.S2LeadInterface.S2CallerFacts
#print AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary
#print AspisR1.OraclePortRuntimeBindingC7.StoredCarrierBinding
#print AspisR1.VTop_OracleCode.Implementation
#print AspisR1.Port1_Driver.rust
