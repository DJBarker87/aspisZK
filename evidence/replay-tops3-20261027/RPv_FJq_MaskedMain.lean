import RPv_FJq_MaskedSourceFormula
import RPv_FJn_MainTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskedMain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.SemSource.terminalValue R0P.Mask.maskClaimsR0
/-- Full installed FIq masked endpoint VALUE on original public/claims/extra/
challenge carriers, with every mask operand tied to its actual source call. -/
theorem value {H : Type} (D : aspis_core.Digest32 H) (pub : FIq_Carriers.Public)
    (claims : FJn_MaskC1Gather.Claims) (alpha : Array MQ 10#usize)
    (extra : Array MQ 29#usize) (c : r1_wire.Challenges)
    (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (row : Array MQ 29#usize)
    (g terminal x mask product sum running : MQ)
    (hc : FJn_MaskC1Gather.CanonClaims claims) (ha : ∀ x∈alpha.val,Canon x)
    (hx : ∀ x∈extra.val,Canon x) (hz : ∀ x∈c.zc.val,Canon x)
    (hl : Canon c.lambda) (hchi : Canon c.chi) (ht : Canon c.theta) (hm : Canon c.mu) (he : Canon c.eta)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native pub))
    (terminalCall : FIq_Terminal.terminal pub claims alpha c=ok (.Ok terminal))
    (rc : OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) claims=ok c1)
    (rm : OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) claims=ok m)
    (rr : Array.index_usize claims 0#usize=ok row) (rg : Array.index_usize row 27#usize=ok g)
    (rx : Array.index_usize extra 28#usize=ok x)
    (maskCall : FIp_SemanticArithmetic.mask c1 m g alpha=ok mask)
    (multiply : FIp_SemanticArithmetic.mul c.eta terminal=ok product)
    (add : FIp_SemanticArithmetic.add mask product=ok sum)
    (finish : FIp_SemanticArithmetic.add sum x=ok running) :
    Canon running ∧ embed (decode running)=
      R0P.Mask.terminalZ (R0P.Mask.maskClaimsR0 ConcretePackBasis.basis)
        (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native pub)))
        (embed (decode c.lambda)) (embed (decode c.chi)) (embed (decode c.theta))
        (embed (decode c.mu)) (embed (decode c.eta))
        (fun i=>embed (FJn_MainPoint.point c.zc i)) ConcretePackBasis.basis
        (fun j l=>embed (FJn_MainClaims.claims claims j l))
        (fun l=>embed (decode (FJq_MainCells.cell extra l)))
        (fun i=>embed (FJn_MainPoint.point alpha i)) := by
  have body:=FJn_MainTerminal.value pub claims alpha c terminal hc ha hz hl hchi ht hm bounds terminalCall
  have masked:=FJq_MaskedSourceFormula.value D claims alpha extra c1 m row g c.eta terminal x mask product sum running
    hc ha hx he body.1 rc rm rr rg rx maskCall multiply add finish
  refine ⟨masked.1,?_⟩
  rw [masked.2,body.2]
  rfl
#print axioms value
end AspisR1.FJq_MaskedMain
end
