import NNV_FinishTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishSameRecords
open RSL

theorem same25 (a : TX1_136.Args NNH_FinishReturns.V) (env : Env)
 (sem : Verified NNH_FinishReturns.V) (head : NNV_FinishCut.Packet a env sem)
 (tail : NNV_FinishTail.Packet a env sem head) : tail.rec25 = tail.rec25' :=
 Except.ok.inj (tail.record25.symm.trans tail.record25')

theorem same26 (a : TX1_136.Args NNH_FinishReturns.V) (env : Env)
 (sem : Verified NNH_FinishReturns.V) (head : NNV_FinishCut.Packet a env sem)
 (tail : NNV_FinishTail.Packet a env sem head) : tail.rec26 = tail.rec26' :=
 Except.ok.inj (tail.record26.symm.trans tail.record26')
#print axioms same25
#print axioms same26
end AspisR1.NNV_FinishSameRecords
end
