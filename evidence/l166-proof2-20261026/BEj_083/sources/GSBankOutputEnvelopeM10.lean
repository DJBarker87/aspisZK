import GSDecoderActualBankM10
import RRCandidateShapeM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSBankOutputEnvelopeM10
open CompPoly GSFixedInputDecoderFamily
open RRConcreteInitialValidStateFromFacts AspisV8R19.OracleFiniteSupport
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
attribute [local irreducible] GSConcreteInterpolation.initial GSConcreteInterpolation.final
  GSConcreteInterpolation.initialState GSConcreteInterpolation.finalState
  GSConcreteRootRecovery.initial GSConcreteRootRecovery.final
  RRTraversalWriterM10.count

@[never_extract,noinline] def candidates : Nat := RRTraversalWriterM10.count 112 1025

def Bounded (out : Results K 5) : Prop := ∀ lane,
  ((out.1 lane).getD []).length ≤ candidates ∧
    ∀ cs ∈ (out.1 lane).getD [], cs.length = 1025

theorem initial_shape (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) :
    ∀ cs ∈ (GSConcreteRootRecovery.initial q t points hs H).getD [], cs.length = 1025 := by
  obtain ⟨Q,hr,hw⟩ := GSConcreteInterpolation.initial_exists points hs
  rw [GSConcreteRootRecovery.initial_eq_recovery q t points hs Q hr H]
  have hh := RRCandidateShapeM10.fixed_recover_shape 112 q t 1025
    (GSConcreteInterpolation.initialState Q)
    (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
    (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H
  cases ho : (RRFixedTapeRecovery.recover 112 q t 1025
    (GSConcreteInterpolation.initialState Q)
    (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
    (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2 H).1 with
  | none => simp only [Option.getD_none,List.not_mem_nil,IsEmpty.forall_iff,forall_const]
  | some cs => exact hh cs ho

theorem initial_count (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (1025*112)} → Fin t → K × K) :
    ((GSConcreteRootRecovery.initial q t points hs H).getD []).length ≤ candidates := by
  obtain ⟨Q,hr,hw⟩ := GSConcreteInterpolation.initial_exists points hs
  rw [GSConcreteRootRecovery.initial_eq_recovery q t points hs Q hr H]
  let s := GSConcreteInterpolation.initialState Q
  let hd := (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.1
  let hn := (GSConcreteInterpolation.initial_state_contract points hs Q hr).2.2
  have hv := RRRecoveryWorkM10.value 114689 112 q t 1025 s hd hn H
  rw [← hv]
  exact RRActualTraversalWorkM10.candidates 112 q t 1025 (initialValidState 112 s hd hn)
    (extend (Finset.range (1025*112)) H (fun _ => (0,0))) 0 hq

theorem run_bounded (q t : Nat) (inputs : Inputs K 5) (hq : q = Fintype.card K)
    (H : InitialTape K t × FinalTape K t) : Bounded (GSFixedInputDecoderFamily.run q t inputs H) := by
  intro lane
  exact ⟨initial_count q t _ _ hq H.1,initial_shape q t _ _ H.1⟩

theorem actual_bounded (q t : Nat) (inputs : Inputs K 5) (hq : q = Fintype.card K)
    (H : InitialTape K t × FinalTape K t) : Bounded (GSDecoderActualBankM10.run q t inputs H).1 := by
  rw [GSDecoderActualBankM10.run_value]
  exact run_bounded q t inputs hq H

#print axioms initial_shape
#print axioms initial_count
#print axioms run_bounded
#print axioms actual_bounded
end AspisR1.GSBankOutputEnvelopeM10
end
