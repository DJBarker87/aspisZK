import ExtractorProofBindM10
import GSProtocolBasisMirrorM10
import GSInterpolationFullWorkM10
import RRConcreteWriterM10
import GSFixedInputDecoderFamily
import SharedFiniteMaterializationM10

/-! Actual full interpolation and RR traversal over every 29+5 call.
The generic proof-dependent bind prevents concrete interpolation terms from
being normalized when checking the enclosing dependent match. C and T are
explicit per-node/terminal tariffs, whose adequacy is supplied separately. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSDecoderBankWorkM10
open CompPoly GSFixedInputDecoderFamily
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
attribute [local irreducible] GSProtocolBasisMirrorM10.basis
  GSInterpolationFullWorkM10.eval GSConcreteInterpolation.initial GSConcreteInterpolation.final
  GSConcreteInterpolation.initialState GSConcreteInterpolation.finalState
  RRConcreteWriterM10.recover RRTraversalWriterM10.budget

def stateTariff (M : Nat) : Nat := 100*(M+114)^2

def initialInterpolation (points : Array (K × K)) : Option (CBivariate K) × Nat :=
  GSInterpolationFullWorkM10.eval 114689 (GSProtocolBasisMirrorM10.basis 1024 114689 112) points

theorem initialInterpolation_value (points : Array (K × K)) :
    (initialInterpolation points).1 = GSConcreteInterpolation.initial points := by
  unfold initialInterpolation GSConcreteInterpolation.initial
  rw [GSProtocolBasisMirrorM10.value]
  exact GSInterpolationFullWorkM10.value 114689 _ _ GSConcreteInterpolation.initialParams rfl

def initial (q t C T : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) :
    Option (List (List K)) × Nat :=
  let r := ExtractorProofBindM10.bind (GSConcreteInterpolation.initial points)
    (initialInterpolation points) (initialInterpolation_value points) (fun Q hr =>
      let hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
      RRConcreteWriterM10.recover 112 q t C T 1025
        (GSConcreteInterpolation.initialState Q) hc.2.1 hc.2.2 H)
  (r.1,r.2+stateTariff 114689)

theorem initial_value (q t C T : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) :
    (initial q t C T points hs H).1 = GSConcreteRootRecovery.initial q t points hs H := by
  simp only [initial,ExtractorProofBindM10.value,RRConcreteWriterM10.recover_value,
    GSConcreteRootRecovery.initial]

@[noinline, never_extract] def initialBudget (C T : Nat) : Nat :=
  GSInterpolationFullWorkM10.budget 114689 1048576 6480098+
    stateTariff 114689+RRTraversalWriterM10.budget 112 C T 1025

theorem initial_work (q t C T : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) :
    (initial q t C T points hs H).2 ≤ initialBudget C T := by
  have hi := GSInterpolationFullWorkM10.work 114689
    (GSProtocolBasisMirrorM10.basis 1024 114689 112) points
  rw [hs] at hi
  change (initialInterpolation points).2 ≤ _ at hi
  have hn (Q : CBivariate K) (hr : GSConcreteInterpolation.initial points = some Q) :
      (RRConcreteWriterM10.recover 112 q t C T 1025
        (GSConcreteInterpolation.initialState Q)
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H).2 ≤
      RRTraversalWriterM10.budget 112 C T 1025 :=
    RRConcreteWriterM10.recover_work _ _ _ _ _ _ _ _ _ hq H
  have hb := ExtractorProofBindM10.work (GSConcreteInterpolation.initial points)
    (initialInterpolation points) (initialInterpolation_value points)
    (fun Q hr => RRConcreteWriterM10.recover 112 q t C T 1025
      (GSConcreteInterpolation.initialState Q)
      (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
      (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H)
    _ _ hi hn
  rw [GSProtocolBasisMirrorM10.initial_size] at hb
  change _+stateTariff 114689 ≤ _
  unfold initialBudget
  simpa only [Nat.add_right_comm] using Nat.add_le_add_right hb (stateTariff 114689)

def finalInterpolation (points : Array (K × K)) : Option (CBivariate K) × Nat :=
  GSInterpolationFullWorkM10.eval 28673 (GSProtocolBasisMirrorM10.basis 255 28673 112) points

theorem finalInterpolation_value (points : Array (K × K)) :
    (finalInterpolation points).1 = GSConcreteInterpolation.final points := by
  unfold finalInterpolation GSConcreteInterpolation.final
  rw [GSProtocolBasisMirrorM10.value]
  exact GSInterpolationFullWorkM10.value 28673 _ _ GSConcreteInterpolation.finalParams rfl

def final (q t C T : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : {i : Nat // i ∈ Finset.range (256*112)} → Fin t → K × K) :
    Option (List (List K)) × Nat :=
  let r := ExtractorProofBindM10.bind (GSConcreteInterpolation.final points)
    (finalInterpolation points) (finalInterpolation_value points) (fun Q hr =>
      let hc := GSConcreteInterpolation.final_state_contract points hs Q hr
      RRConcreteWriterM10.recover 112 q t C T 256
        (GSConcreteInterpolation.finalState Q) hc.2.1 hc.2.2 H)
  (r.1,r.2+stateTariff 28673)

theorem final_value (q t C T : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : {i : Nat // i ∈ Finset.range (256*112)} → Fin t → K × K) :
    (final q t C T points hs H).1 = GSConcreteRootRecovery.final q t points hs H := by
  simp only [final,ExtractorProofBindM10.value,RRConcreteWriterM10.recover_value,
    GSConcreteRootRecovery.final]

@[noinline, never_extract] def finalBudget (C T : Nat) : Nat :=
  GSInterpolationFullWorkM10.budget 28673 262144 1626522+
    stateTariff 28673+RRTraversalWriterM10.budget 112 C T 256

theorem final_work (q t C T : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (256*112)} → Fin t → K × K) :
    (final q t C T points hs H).2 ≤ finalBudget C T := by
  have hi := GSInterpolationFullWorkM10.work 28673
    (GSProtocolBasisMirrorM10.basis 255 28673 112) points
  rw [hs] at hi
  change (finalInterpolation points).2 ≤ _ at hi
  have hn (Q : CBivariate K) (hr : GSConcreteInterpolation.final points = some Q) :
      (RRConcreteWriterM10.recover 112 q t C T 256
        (GSConcreteInterpolation.finalState Q)
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.1
        (GSConcreteInterpolation.final_state_contract points hs Q hr).2.2 H).2 ≤
      RRTraversalWriterM10.budget 112 C T 256 :=
    RRConcreteWriterM10.recover_work _ _ _ _ _ _ _ _ _ hq H
  have hb := ExtractorProofBindM10.work (GSConcreteInterpolation.final points)
    (finalInterpolation points) (finalInterpolation_value points)
    (fun Q hr => RRConcreteWriterM10.recover 112 q t C T 256
      (GSConcreteInterpolation.finalState Q)
      (GSConcreteInterpolation.final_state_contract points hs Q hr).2.1
      (GSConcreteInterpolation.final_state_contract points hs Q hr).2.2 H)
    _ _ hi hn
  rw [GSProtocolBasisMirrorM10.final_size] at hb
  change _+stateTariff 28673 ≤ _
  unfold finalBudget
  simpa only [Nat.add_right_comm] using Nat.add_le_add_right hb (stateTariff 28673)

def run (q t C T : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) :
    Results K 5 × Nat :=
  let a := SharedFiniteMaterializationM10.batch (fun i : Fin 29 =>
    initial q t C T (inputs.initialPoints i) (inputs.initialSize i) H.1)
  let b := SharedFiniteMaterializationM10.batch (fun i : Fin 5 =>
    final q t C T (inputs.finalPoints i) (inputs.finalSize i) H.2)
  ((a.1,b.1),a.2+b.2+2)

attribute [local irreducible] SharedFiniteMaterializationM10.batch

theorem run_value (q t C T : Nat) (inputs : Inputs K 5) (H : InitialTape K t × FinalTape K t) :
    (run q t C T inputs H).1 = GSFixedInputDecoderFamily.run q t inputs H := by
  unfold run GSFixedInputDecoderFamily.run
  dsimp only
  congr 1
  · funext i
    exact (SharedFiniteMaterializationM10.value _ i).trans (initial_value _ _ _ _ _ _ _)
  · funext i
    exact (SharedFiniteMaterializationM10.value _ i).trans (final_value _ _ _ _ _ _ _)

@[noinline, never_extract] def bankBudget (C T : Nat) : Nat :=
  29*(initialBudget C T+3)+5*(finalBudget C T+3)+4

theorem add_batch (x y A B : Nat) (hx : x ≤ A+1) (hy : y ≤ B+1) :
    x+y+2 ≤ A+B+4 := by omega

theorem run_work (q t C T : Nat) (inputs : Inputs K 5) (hq : q = Fintype.card K)
    (H : InitialTape K t × FinalTape K t) : (run q t C T inputs H).2 ≤ bankBudget C T := by
  have ha := SharedFiniteMaterializationM10.work
    (fun i : Fin 29 => initial q t C T (inputs.initialPoints i) (inputs.initialSize i) H.1)
    (initialBudget C T) (fun i => initial_work _ _ _ _ _ _ hq _)
  have hb := SharedFiniteMaterializationM10.work
    (fun i : Fin 5 => final q t C T (inputs.finalPoints i) (inputs.finalSize i) H.2)
    (finalBudget C T) (fun i => final_work _ _ _ _ _ _ hq _)
  exact add_batch _ _ _ _ ha hb

#print axioms initialInterpolation_value
#print axioms initial_value
#print axioms initial_work
#print axioms finalInterpolation_value
#print axioms final_value
#print axioms final_work
#print axioms run_value
#print axioms add_batch
#print axioms run_work
end AspisR1.GSDecoderBankWorkM10
end
