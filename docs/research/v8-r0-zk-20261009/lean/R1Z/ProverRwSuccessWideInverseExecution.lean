import R1Z.ProverRwSuccessWideSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessWideInverseExecution
open Aeneas Aeneas.Std Result ProverRwDictionaryTower

theorem execute (x out : W) (a b ub norm ni lo nb hi : Q)
    (ha : qMul x.c0 x.c0=.ok a) (hb : qMul x.c1 x.c1=.ok b)
    (hub : qMul ProverRwSuccessWideSource.u b=.ok ub)
    (hnorm : qSub a ub=.ok norm)
    (hni : ProverRwSuccessInverseInstall.Src.qInv norm=.ok (some ni))
    (hlo : qMul x.c0 ni=.ok lo)
    (hnb : ProverRwSuccessInverseInstall.Src.qNeg x.c1=.ok nb)
    (hhi : qMul nb ni=.ok hi)
    (hout : ProverRwSuccessWideSource.construct lo hi=.ok out) :
    ProverRwSuccessWideSource.inverse x=.ok (some out) := by
  simp only [ProverRwSuccessWideSource.inverse,ha,hb,hub,hnorm,hni,hlo,hnb,hhi,hout,
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok]
#print axioms execute
end R1Z.ProverRwSuccessWideInverseExecution
