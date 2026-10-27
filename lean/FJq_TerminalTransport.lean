import FJq_LiteralOperands
import FJn_MainTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_TerminalTransport
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticArithmetic (MQ)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.SemSource.terminalValue
/-- Transport of the checked actual body to exactly the literal public, Y and
challenges. Operand joins are explicit local obligations, not new top owners. -/
theorem value (pub : FIq_Carriers.Public)
    (claims : Array (Array MQ 29#usize) 3#usize) (alpha : Array MQ 10#usize)
    (c : r1_wire.Challenges) (out : MQ)
    (hc : ∀ row∈claims.val,∀ x∈row.val,FIp_SemanticValues.Canon x)
    (ha : ∀ x∈alpha.val,FIp_SemanticValues.Canon x)
    (hz : ∀ x∈c.zc.val,FIp_SemanticValues.Canon x)
    (hl : FIp_SemanticValues.Canon c.lambda) (hchi : FIp_SemanticValues.Canon c.chi)
    (ht : FIp_SemanticValues.Canon c.theta) (hm : FIp_SemanticValues.Canon c.mu)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native pub))
    (run : FIq_Terminal.terminal pub claims alpha c=ok (.Ok out))
    (literalPub : R0P.Public SemanticPublicWire.M31) (v : LiteralOpeningView.View)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (publicSame : SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native pub))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub)
    (claimsSame : (fun j l=>embed (FJn_MainClaims.claims claims j l))=
      fun j l=>data.Y ⟨j.val,by omega⟩ l)
    (challengesSame : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha) :
    FIp_SemanticValues.Canon out ∧ embed (FIp_SemanticValues.decode out)=
      R0P.SemSource.terminalValue (SpendDataMap.mapPublic ExactBaseProjection.embed literalPub)
        (FJq_LiteralOperands.challenge v 0) (FJq_LiteralOperands.challenge v 1)
        (FJq_LiteralOperands.challenge v 2) (FJq_LiteralOperands.challenge v 13)
        (R0P.SemSource.preZc (fun j=>FJq_LiteralOperands.challenge v j.val))
        ConcretePackBasis.basis (fun j l=>data.Y ⟨j.val,by omega⟩ l)
        (fun i=>FJq_LiteralOperands.challenge v (15+i.val)) := by
  have actual:=FJn_MainTerminal.value pub claims alpha c out hc ha hz hl hchi ht hm bounds run
  obtain ⟨lam,chi,theta,mu,eta,zc,point⟩:=FJq_LiteralOperands.value c alpha v challengesSame
  refine ⟨actual.1,?_⟩
  rw [actual.2,publicSame,claimsSame,lam,chi,theta,mu,zc,point]
#print axioms value
end AspisR1.FJq_TerminalTransport
end
