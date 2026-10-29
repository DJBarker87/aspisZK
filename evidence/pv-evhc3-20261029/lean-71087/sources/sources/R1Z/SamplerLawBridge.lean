import R1Z.Sem1UniformR1
import R1Z.SamplerLawIface

/-! The interface law (`R1Z.SamplerLawIface`, produced on the spend-path base by
`R1J.SamplerLawSpend.qm31SamplerLaw_spend`) is the D47.2 premise `QM31SamplerLaw` of
`Sem1UniformR1`, field by field.  Privacy base only; the composition with the spend-path
producer needs one base for both (DESIGN-BUILD-INTEGRATION §4 (f)). -/

set_option autoImplicit false

namespace R1Z.SamplerLawBridge

open R1Z.Sem1UniformR1

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def toSem1 {s1 : R0Z.FsStatement.OracleAnswer → K}
    (L : R1Z.SamplerLawIface.QM31SamplerLaw s1) : QM31SamplerLaw s1 where
  rank := L.rank
  emb := L.emb
  emb_inj := L.emb_inj
  sample := L.sample

end R1Z.SamplerLawBridge

#print axioms R1Z.SamplerLawBridge.toSem1
