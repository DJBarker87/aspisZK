import GSConcreteInterpolation
import RRFixedTapeRecovery

set_option autoImplicit false
namespace AspisR1.GSConcreteRootRecovery
open CompPoly Polynomial RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRProgramRecoveryContracts
open AspisR1.CompPolyFactorMeanTools
open AspisV8R19.OracleResampling AspisV8PairedCommitment

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def initial (q t : Nat) (points : Array (K × K)) (hs : points.size = 1048576)
    (H : {i : Nat // i ∈ Finset.range (1025 * 112)} → Fin t → K × K) :
    Option (List (List K)) :=
  match hr : GSConcreteInterpolation.initial points with
  | none => none
  | some Q =>
    let hc := GSConcreteInterpolation.initial_state_contract points hs Q hr
    (RRFixedTapeRecovery.recover 112 q t 1025 (GSConcreteInterpolation.initialState Q)
      hc.2.1 hc.2.2 H).1

#check initial

def final (q t : Nat) (points : Array (K × K)) (hs : points.size = 262144)
    (H : {i : Nat // i ∈ Finset.range (256 * 112)} → Fin t → K × K) :
    Option (List (List K)) :=
  match hr : GSConcreteInterpolation.final points with
  | none => none
  | some Q =>
    let hc := GSConcreteInterpolation.final_state_contract points hs Q hr
    (RRFixedTapeRecovery.recover 112 q t 256 (GSConcreteInterpolation.finalState Q)
      hc.2.1 hc.2.2 H).1


#print axioms initial
#print axioms final
end AspisR1.GSConcreteRootRecovery
