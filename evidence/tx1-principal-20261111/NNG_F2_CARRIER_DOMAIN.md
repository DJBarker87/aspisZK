# NNG-F2: projection must respect LIB canonical carriers

Target not yet established. Provisional-interface finding, no row credit.

The committed LIB_VScalarCarriers.QM31 carrier is the canonical subtype of
NQ. A total injective projection from every four-u32 raw QM31 record into
that subtype cannot be used: it would inject 2^128 limb representations
into at most 2^124 canonical values. The old NNG_Projection136 global q_injective
condition is valid as a conditional theorem interface for other VLib choices,
but cannot instantiate the intended LIB scalar carrier. No candidate uses it.

The corrected NNG_DProjection136 maps are faithful only on qDom. The fold
must derive qDom for the two actually compared scalar values from CLOSED134's
returned model and the reached CLOSED add result, then use domain-local
injectivity at the terminal guard. These are internal returned-arm facts,
not new finishInputDom clauses or caller-supplied successful-child premises.

LIB's Prefix also retains source bytes and its parser proof. The fold keeps
the original semantic argument a.prefix_ throughout; it does not assume a
global inverse from a raw Prefix recovers the caller's chosen provenance.
NNG_DProjection136.Inputs records only the original struct-field links needed
for eta, challenges and c1_root; each child graph law still proves its SAME
actual argument association. No VLib field instance or spec is changed.

Superseded for the intended installation: NNG_Projection136.Representation,
NNG_EnvObserved136.Target and the source suffix proofs parameterized by that
stronger record. Their proofs remain supporting conditional facts. The new
domain-aware producer and source fold will use DProjection136 instead.
