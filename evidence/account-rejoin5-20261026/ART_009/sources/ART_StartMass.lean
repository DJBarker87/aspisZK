import ART_StartCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_StartMass
open FS FS2 AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier
attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad

theorem bound {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (a : Adversary A) (Q0 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0) :
    lazyMean (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a)))) emptyTable
      (fun run => indicator (F3T_Clean.prefixHit D (lift c (submission a)) run)) ≤
      ((Q0+34 : Nat) : Rat)*PerAttemptEnvelope.B := by
  have hq : ∀ H : Bytes → State, (eval H (lift c (submission a))).1.length ≤ Q0 := by
    intro H
    rw [lift_eval,submission_eval]
    exact prefixBound H
  exact F3T_Probability.restricted_union_bound D (lift c (submission a)) Q0 hq

#print axioms bound
end AspisR1.ART_StartMass
end
