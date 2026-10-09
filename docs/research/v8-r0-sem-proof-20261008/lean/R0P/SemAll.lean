import R0P.Asset
import R0P.CircleSampler
import R0P.Copy
import R0P.CopyConstants
import R0P.CopyInputLinks
import R0P.CopyRegistry
import R0P.Core
import R0P.CoreExt
import R0P.Digest
import R0P.EmptyRoots
import R0P.Extraction
import R0P.LaneMap
import R0P.LogUpAssembly
import R0P.LogUpChain
import R0P.LogUpCompress
import R0P.LogUpFrac
import R0P.MessageDescent
import R0P.Occupancy
import R0P.Path
import R0P.Poseidon
import R0P.PoseidonConstants
import R0P.Positive
import R0P.Positivity
import R0P.PositivityChain
import R0P.PositivityWired
import R0P.Schedule
import R0P.SemAccept
import R0P.SemAssembly
import R0P.SemBadSets
import R0P.SemBridge
import R0P.SemCharP
import R0P.SemClosed
import R0P.SemD2
import R0P.SemD2Glue
import R0P.SemD3
import R0P.SemD3Glue
import R0P.SemDecision
import R0P.SemDeg
import R0P.SemDegFamilies
import R0P.SemDuplexDecoder
import R0P.SemDuplexDecodes
import R0P.SemDuplexDensity
import R0P.SemFiatShamir
import R0P.SemHonest
import R0P.SemLedger
import R0P.SemMaxErr
import R0P.SemPad
import R0P.SemRounds
import R0P.SemSource
import R0P.SemView
import R0P.SemVirtualDeg
import R0P.Semantics
import R0P.Sumcheck
import R0P.Value
import R0P.Zerocheck

/-! Frozen semantic proof manifest. Import every R0P source module and audit
the final composition and the seven requested supporting obligations. -/

#print axioms R0P.SemDuplex.combined_fiat_shamir_closed
#print axioms R0P.SemSource.combinedProtocol_D2
#print axioms R0P.SemD3Glue.d3
#print axioms R0P.SemSource.virtualDeg
#print axioms R0P.SemSource.honestRows
#print axioms R0P.SemSource.checksAccept
#print axioms R0P.SemSource.circleSample0_mass
#print axioms R0P.SemSource.circleSample1_mass
