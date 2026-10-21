import InterpolationAllocationM10
import RRTraversalAllocationM10
import AllocationProofBindM10
import GSDecoderActualBankM10
import GSByteBankWorkM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSBankAllocationM10
open CompPoly GSFixedInputDecoderFamily AspisWideTower
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
attribute [local irreducible] GSProtocolBasisMirrorM10.basis GSInterpolationFullWorkM10.eval
  RRRecoveryWorkM10.recover GSConcreteInterpolation.initial GSConcreteInterpolation.final
  GSDecoderActualBankM10.initialInterpolation GSDecoderActualBankM10.finalInterpolation
  InterpolationAllocationM10.cells RRTraversalAllocationM10.recoveryCells

def initialCells (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) : Nat :=
  AllocationProofBindM10.cells (GSConcreteInterpolation.initial points)
    (GSDecoderActualBankM10.initialInterpolation points) (GSDecoderActualBankM10.initialInterpolation_value points)
    (fun Q hr =>
      let hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
      RRRecoveryWorkM10.recover 114689 112 q t 1025
        (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H)
    (InterpolationAllocationM10.cells 114689 (GSProtocolBasisMirrorM10.basis 1024 114689 112) points)
    (fun Q hr =>
      let hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
      RRTraversalAllocationM10.recoveryCells 114689 112 q t 1025
        (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H)+
    4*6480098+10*(114689+114)^2

theorem initial_paid (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) :
    initialCells q t points hs H ≤ (GSDecoderActualBankM10.initial q t points hs H).2 := by
  have hi : InterpolationAllocationM10.cells 114689 (GSProtocolBasisMirrorM10.basis 1024 114689 112) points ≤
      (GSDecoderActualBankM10.initialInterpolation points).2 := by
    unfold GSDecoderActualBankM10.initialInterpolation
    exact InterpolationAllocationM10.paid _ _ _
  have hb := AllocationProofBindM10.paid (GSConcreteInterpolation.initial points)
    (GSDecoderActualBankM10.initialInterpolation points) (GSDecoderActualBankM10.initialInterpolation_value points)
    (fun Q hr =>
      let hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
      RRRecoveryWorkM10.recover 114689 112 q t 1025 (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H)
    _ _ hi (fun Q hr => RRTraversalAllocationM10.recovery_paid _ _ _ _ _ _ _ _ _)
  have hc : 4*6480098+10*(114689+114)^2 ≤ GSDecoderActualBankM10.stateTariff 114689 := by
    unfold GSDecoderActualBankM10.stateTariff
    omega
  simpa only [initialCells,GSDecoderActualBankM10.initial,Nat.add_assoc] using Nat.add_le_add hb hc

def finalCells (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : {i : Nat // i ∈ Finset.range (256*112)} → Fin t → K × K) : Nat :=
  AllocationProofBindM10.cells (GSConcreteInterpolation.final points)
    (GSDecoderActualBankM10.finalInterpolation points) (GSDecoderActualBankM10.finalInterpolation_value points)
    (fun Q hr =>
      let hc := GSConcreteInterpolation.final_state_contract points hs Q hr
      RRRecoveryWorkM10.recover 28673 112 q t 256
        (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H)
    (InterpolationAllocationM10.cells 28673 (GSProtocolBasisMirrorM10.basis 255 28673 112) points)
    (fun Q hr =>
      let hc := GSConcreteInterpolation.final_state_contract points hs Q hr
      RRTraversalAllocationM10.recoveryCells 28673 112 q t 256
        (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H)+
    4*1626522+10*(28673+114)^2

theorem final_paid (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : {i : Nat // i ∈ Finset.range (256*112)} → Fin t → K × K) :
    finalCells q t points hs H ≤ (GSDecoderActualBankM10.final q t points hs H).2 := by
  have hi : InterpolationAllocationM10.cells 28673 (GSProtocolBasisMirrorM10.basis 255 28673 112) points ≤
      (GSDecoderActualBankM10.finalInterpolation points).2 := by
    unfold GSDecoderActualBankM10.finalInterpolation
    exact InterpolationAllocationM10.paid _ _ _
  have hb := AllocationProofBindM10.paid (GSConcreteInterpolation.final points)
    (GSDecoderActualBankM10.finalInterpolation points) (GSDecoderActualBankM10.finalInterpolation_value points)
    (fun Q hr =>
      let hc := GSConcreteInterpolation.final_state_contract points hs Q hr
      RRRecoveryWorkM10.recover 28673 112 q t 256 (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H)
    _ _ hi (fun Q hr => RRTraversalAllocationM10.recovery_paid _ _ _ _ _ _ _ _ _)
  have hc : 4*1626522+10*(28673+114)^2 ≤ GSDecoderActualBankM10.stateTariff 28673 := by
    unfold GSDecoderActualBankM10.stateTariff
    omega
  simpa only [finalCells,GSDecoderActualBankM10.final,Nat.add_assoc] using Nat.add_le_add hb hc

def bankCells (q t : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) : Nat :=
  AllocationBatchM10.cells (fun i : Fin 29 => initialCells q t (inputs.initialPoints i) (inputs.initialSize i) H.1)+
  AllocationBatchM10.cells (fun i : Fin 5 => finalCells q t (inputs.finalPoints i) (inputs.finalSize i) H.2)+2

theorem bank_paid (q t : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) :
    bankCells q t inputs H ≤ (GSDecoderActualBankM10.run q t inputs H).2 := by
  have ha := AllocationBatchM10.batch_work
    (fun i : Fin 29 => GSDecoderActualBankM10.initial q t (inputs.initialPoints i) (inputs.initialSize i) H.1)
    _ (fun i => initial_paid _ _ _ _ _)
  have hb := AllocationBatchM10.batch_work
    (fun i : Fin 5 => GSDecoderActualBankM10.final q t (inputs.finalPoints i) (inputs.finalSize i) H.2)
    _ (fun i => final_paid _ _ _ _ _)
  exact Nat.add_le_add_right (Nat.add_le_add ha hb) 2


#print axioms initial_paid
#print axioms final_paid
#print axioms bank_paid
end AspisR1.GSBankAllocationM10
end
