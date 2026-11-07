import NNG_LIBData
import NNG_LIBDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteInput136
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport
open NNG_LIBArrays NNG_LIBScalar

/-- Exactly one original input and environment, with the arbitrary raw
observer retained. No model result is an input or caller hypothesis. -/
def input (pub : LIB_VCarriers.Public) (pre : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (challenges : LIB_VCarriers.Challenges)
    (observer : Observer) (env : RSL.Env) : Parent Unit Unit where
  digest := NNG_LIBDigest.digest env
  publicValue := NNG_LIBData.lowerPublic pub
  prefixValue := NNG_LIBData.lowerPrefix pre
  transcript := fromT10 t
  challenges := lowerChallenges challenges
  observer := observer
  world := ()

theorem public_exact (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : Observer) (env : RSL.Env) :
    toT9 (input pub p t c obs env).publicValue = pub := NNG_LIBData.public_exact pub
#print axioms public_exact

theorem prefix_exact (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : Observer) (env : RSL.Env) :
    toT12 (input pub p t c obs env).prefixValue = LIB_VCarriers.prefixRaw p := NNG_LIBData.prefix_exact p
#print axioms prefix_exact

theorem transcript_exact (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : Observer) (env : RSL.Env) :
    toT10 (input pub p t c obs env).transcript = t := fromT10_inverse t
#print axioms transcript_exact

theorem challenges_exact (fallback : Value) (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : Observer) (env : RSL.Env) :
    projectChallenges fallback (input pub p t c obs env).challenges = c := project_lower_challenges fallback c
#print axioms challenges_exact
end AspisR1.NNG_ConcreteInput136
