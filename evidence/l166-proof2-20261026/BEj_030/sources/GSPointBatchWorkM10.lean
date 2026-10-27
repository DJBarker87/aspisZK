import SharedFiniteMaterializationM10
import GSConcreteReceivedWordInputs

/-! Eager construction of all received-point arrays. Cached word reads and
fixed-domain point generation use a conservative 10^12-step primitive tariff:
indices are at most 20 bits, field words are fixed width, and the only extra
initial multiplier has the fixed exponents 2 and 512. Lane arrays are retained
before the bank runs, so later consumers do not rebuild them. -/
set_option autoImplicit false
namespace AspisR1.GSPointBatchWorkM10
open AspisWideTower AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open GSFixedInputDecoderFamily

def initial (W : InitialWord WideExact) : Array (WideExact × WideExact) × Nat :=
  BinTypedWordDemandWork.materialize (fun i : Fin 1048576 =>
    ((initialRuntimePoint i,(1+initialRuntimePoint i^2)^512*W i),1000000000000))

def final (V : FinalWord WideExact) : Array (WideExact × WideExact) × Nat :=
  BinTypedWordDemandWork.materialize (fun i : Fin 262144 =>
    ((finalRuntimePoint i,V i),1000000000000))

attribute [local irreducible] Array.ofFn initialRuntimePoint finalRuntimePoint

theorem initial_value (W : InitialWord WideExact) :
    (initial W).1 = AspisWide.GSConcreteReceivedWordPoints.initialPoints W := by
  simp only [initial,BinTypedWordDemandWork.materialize,
    AspisWide.GSConcreteReceivedWordPoints.initialPoints]

theorem final_value (V : FinalWord WideExact) :
    (final V).1 = AspisWide.GSConcreteReceivedWordPoints.finalPoints V := by
  simp only [final,BinTypedWordDemandWork.materialize,
    AspisWide.GSConcreteReceivedWordPoints.finalPoints]

theorem initial_size (W : InitialWord WideExact) : (initial W).1.size = 1048576 :=
  BinTypedWordDemandWork.materialize_size _

theorem final_size (V : FinalWord WideExact) : (final V).1.size = 262144 :=
  BinTypedWordDemandWork.materialize_size _

theorem initial_work (W : InitialWord WideExact) :
    (initial W).2 ≤ 1048576*(1000000000000+3)+1 :=
  BinTypedWordDemandWork.materialize_work _ _ (fun _ => Nat.le_refl _)

theorem final_work (V : FinalWord WideExact) :
    (final V).2 ≤ 262144*(1000000000000+3)+1 :=
  BinTypedWordDemandWork.materialize_work _ _ (fun _ => Nat.le_refl _)

def inputs (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact) :
    Inputs WideExact 5 × Nat :=
  let a := SharedFiniteMaterializationM10.batch (fun i => initial (W i))
  let b := SharedFiniteMaterializationM10.batch (fun i => final (V i))
  (⟨a.1,fun i => by rw [SharedFiniteMaterializationM10.value]; exact initial_size _,
    b.1,fun i => by rw [SharedFiniteMaterializationM10.value]; exact final_size _⟩,
    a.2+b.2+4)

attribute [local irreducible] SharedFiniteMaterializationM10.batch

theorem inputs_value (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact) :
    (inputs W V).1 = AspisWide.GSConcreteReceivedWordInputs.fromWords W V := by
  unfold inputs AspisWide.GSConcreteReceivedWordInputs.fromWords
  dsimp only
  congr 1
  · funext i
    exact (SharedFiniteMaterializationM10.value _ i).trans (initial_value (W i))
  · funext i
    exact (SharedFiniteMaterializationM10.value _ i).trans (final_value (V i))

def budget : Nat :=
  29*(1048576*(1000000000000+3)+1+3)+5*(262144*(1000000000000+3)+1+3)+6

theorem inputs_work (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact) :
    (inputs W V).2 ≤ budget := by
  have ha := SharedFiniteMaterializationM10.work (fun i : Fin 29 => initial (W i)) _
    (fun i => initial_work (W i))
  have hb := SharedFiniteMaterializationM10.work (fun i : Fin 5 => final (V i)) _
    (fun i => final_work (V i))
  change _+_+4 ≤ _
  unfold budget
  omega

#print axioms initial_value
#print axioms final_value
#print axioms initial_size
#print axioms final_size
#print axioms initial_work
#print axioms final_work
#print axioms inputs_value
#print axioms inputs_work
end AspisR1.GSPointBatchWorkM10
