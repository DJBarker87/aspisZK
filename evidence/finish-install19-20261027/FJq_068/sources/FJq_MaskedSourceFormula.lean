import FJq_MaskC1Value
import FJq_MaskOnlyValue
import FJq_ClaimRead
import FJn_MaskedWideValue
import FJn_MaskOnlyGather
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskedSourceFormula
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.Mask.maskValue
/-- Source mask arithmetic as maskClaimsR0 on the SAME original claim/extra
rows. All gather/value associations are derived from actual calls. -/
theorem value {H : Type} (D : aspis_core.Digest32 H)
    (claims : FJn_MaskC1Gather.Claims) (alpha : Array MQ 10#usize)
    (extra : Array MQ 29#usize) (c1 : Array MQ 16#usize) (m : Array MQ 10#usize)
    (row : Array MQ 29#usize) (g eta terminal x mask product sum running : MQ)
    (hc : FJn_MaskC1Gather.CanonClaims claims) (ha : ∀ x∈alpha.val,Canon x)
    (hx : ∀ x∈extra.val,Canon x) (he : Canon eta) (ht : Canon terminal)
    (rc : OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) claims=ok c1)
    (rm : OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) claims=ok m)
    (rr : Array.index_usize claims 0#usize=ok row)
    (rg : Array.index_usize row 27#usize=ok g)
    (rx : Array.index_usize extra 28#usize=ok x)
    (maskCall : FIp_SemanticArithmetic.mask c1 m g alpha=ok mask)
    (multiply : FIp_SemanticArithmetic.mul eta terminal=ok product)
    (add : FIp_SemanticArithmetic.add mask product=ok sum)
    (finish : FIp_SemanticArithmetic.add sum x=ok running) :
    Canon running ∧ embed (decode running)=
      R0P.Mask.maskClaimsR0 ConcretePackBasis.basis
        (fun l=>embed (FJn_MainClaims.claims claims 0 l))
        (fun l=>embed (decode (FJq_MainCells.cell extra l)))
        (fun i=>embed (FJn_MainPoint.point alpha i)) +embed (decode eta)*embed (decode terminal) := by
  have rowCan : ∀ x∈row.val,Canon x := hc row (FIr_ArrayRead.member claims 0#usize row rr)
  have gc:=FJn_MainArrayValue.canonical row 27#usize g rowCan rg
  have xc:=FJn_MainArrayValue.canonical extra 28#usize x hx rx
  have actual:=FJn_MaskedWideValue.value c1 m g alpha eta terminal x mask product sum running
    (FJn_MaskC1Gather.canonical D claims c1 hc rc)
    (FJn_MaskOnlyGather.canonical D claims m hc rm) ha gc he ht xc maskCall multiply add finish
  have gv:=FJq_ClaimRead.value claims 0 27 row g rr rg
  have xv : decode x=decode (FJq_MainCells.cell extra 28) := by
    have read:=FJn_MainArrayValue.read extra 28#usize x rx
    exact read.symm.trans (FJq_MainCells.bounded extra 28)
  have point : FJn_MaskWide.cell10 alpha=fun i=>embed (FJn_MainPoint.point alpha i) :=
    funext (FJq_MainCells.point alpha)
  refine ⟨actual.1,?_⟩
  rw [actual.2,FJq_MaskC1Value.value D claims c1 rc,FJq_MaskOnlyValue.value D claims m rm,gv,xv,point]
  unfold R0P.Mask.maskClaimsR0
  ring
#print axioms value
end AspisR1.FJq_MaskedSourceFormula
end
