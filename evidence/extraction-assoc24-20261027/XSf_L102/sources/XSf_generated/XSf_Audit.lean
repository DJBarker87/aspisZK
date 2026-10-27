import XSf_A2
import XSf_A3Narrowed
import XSf_A3NativePowers
import XSf_A3Ports
import XSf_A3Powers
import XSf_A3Produced
import XSf_A3Trace
import XSf_ByteDomain
import XSf_CheckedCanonical
import XSf_Closed
import XSf_DotObserved
import XSf_LaneDomain
import XSf_Nonvacuity
import XSf_ParserWitness
import XSf_PartObserved
import XSf_PrepareClaim
import XSf_PrepareSemantic
import XSf_PrepareTrace
import XSf_PrepareY1
import XSf_Reached
import XSf_ReachedScratch
import XSf_SemReads
import XSf_View
import XSf_Y1Produced

#print axioms XSf_A2.reached_prepare
#print axioms XSf_A2.whole
#print axioms XSf_A3Narrowed.trace
#print axioms XSf_A3NativePowers.map_back
#print axioms XSf_A3NativePowers.observed
#print axioms XSf_A3Ports.roundtrip
#print axioms XSf_A3Ports.canonical
#print axioms XSf_A3Ports.weights
#print axioms XSf_A3Powers.observed_weights
#print axioms XSf_A3Powers.weighted
#print axioms XSf_A3Powers.claim_at_call
#print axioms XSf_A3Produced.trace
#print axioms XSf_A3Trace.construct
#print axioms XSf_ByteDomain.word_at
#print axioms XSf_ByteDomain.decoded
#print axioms XSf_ByteDomain.from_decoders
#print axioms XSf_CheckedCanonical.valid
#print axioms XSf_CheckedCanonical.array29
#print axioms XSf_Closed.prepare
#print axioms XSf_DotObserved.reads
#print axioms XSf_LaneDomain.selected
#print axioms XSf_LaneDomain.from_lanes
#print axioms XSf_Nonvacuity.powers_and_sum
#print axioms XSf_ParserWitness.parsed_zero
#print axioms XSf_ParserWitness.parse_inhabited
#print axioms XSf_ParserWitness.serializer_counterexample
#print axioms XSf_PartObserved.raw_reads
#print axioms XSf_PartObserved.typed_reads
#print axioms XSf_PrepareClaim.change_claim
#print axioms XSf_PrepareSemantic.produced
#print axioms XSf_PrepareTrace.from_prepare
#print axioms XSf_PrepareY1.produced
#print axioms XSf_PrepareY1.trace
#print axioms XSf_Reached.kappa
#print axioms XSf_Reached.parsed
#print axioms XSf_ReachedScratch.tail_powers
#print axioms XSf_ReachedScratch.produced
#print axioms XSf_SemReads.canonical
#print axioms XSf_View.inactive
#print axioms XSf_Y1Produced.part_lanes
#print axioms XSf_Y1Produced.dot_domain

set_option pp.all true in
#check @XSf_Closed.prepare
set_option pp.all true in
#check @XSf_A3Narrowed.trace
