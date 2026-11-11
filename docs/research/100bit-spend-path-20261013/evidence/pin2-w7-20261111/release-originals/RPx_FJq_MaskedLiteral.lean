import RPv_FJq_LiteralOperands
import RPx_FJq_MaskedMain
import R3SemanticRemainingJoins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MaskedLiteral
open Aeneas Aeneas.Std AspisR1PublicPreparation
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (decode)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.Mask.terminalZ R0P.Mask.maskClaimsR0
/-- Operand-only transport of the full native formula into the literal SAME
public/Y/challenges terminal. The source VALUE is supplied by MaskedMain. -/
theorem transport (pub : FIq_Carriers.Public) (claims : FJn_MaskC1Gather.Claims)
    (alpha : Array MQ 10#usize) (extra : Array MQ 29#usize) (c : r1_wire.Challenges)
    (literalPub : R0P.Public SemanticPublicWire.M31) (v : LiteralOpeningView.View)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (publicSame : SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native pub))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub)
    (claimsSame : (fun j l=>embed (FJn_MainClaims.claims claims j l))=
      fun j l=>data.Y ⟨j.val,by omega⟩ l)
    (extraSame : (fun l : Fin 29=>embed (decode (FJq_MainCells.cell extra l)))=data.Y 3)
    (challengesSame : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha) :
    R0P.Mask.terminalZ (R0P.Mask.maskClaimsR0 ConcretePackBasis.basis)
      (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native pub)))
      (embed (decode c.lambda)) (embed (decode c.chi)) (embed (decode c.theta))
      (embed (decode c.mu)) (embed (decode c.eta))
      (fun i=>embed (FJn_MainPoint.point c.zc i)) ConcretePackBasis.basis
      (fun j l=>embed (FJn_MainClaims.claims claims j l))
      (fun l=>embed (decode (FJq_MainCells.cell extra l)))
      (fun i=>embed (FJn_MainPoint.point alpha i))=R3SemanticRemainingJoins.terminal literalPub v data := by
  obtain ⟨lam,chi,theta,mu,eta,zc,point⟩:=FJq_LiteralOperands.value c alpha v challengesSame
  unfold R3SemanticRemainingJoins.terminal
  rw [publicSame,claimsSame,extraSame,←lam,←chi,←theta,←mu,←eta,←zc,←point]
  rfl
#print axioms transport
end AspisR1.FJq_MaskedLiteral
end
