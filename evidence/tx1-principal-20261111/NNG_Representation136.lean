import LIB_VLib
import NNG_DEnvObserved136
import NNG_ConcreteInput136
import NNG_ConcreteCalls136
import NNG_LIBEvents136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Representation136
open Aeneas Aeneas.Std Result NNG_Emitted NNG_Transport
open NNG_DProjection136 NNG_LIBScalar NNG_LIBArrays
abbrev VL := LIB_VLib.library
abbrev Args := RSL.TX1_136.Args VL

/-- Output interpretation for the LIB-owned concrete library. No VLib field
or Child is defined here; total raw scalar projection is faithful on Domain. -/
def project (a : Args) : Representation VL Unit where
  transcript := toT10
  challenges := projectChallenges a.challenges.eta
  q := NNG_LIBScalar.project a.challenges.eta
  alpha := projectArray a.challenges.eta
  claims := projectClaims a.challenges.eta
  k29 := projectArray a.challenges.eta
  point := toT2
  record := toT14
  error := toT13
  bytes := LIB_Carriers.bytes
  b32 := LIB_Carriers.b32
  qDom := Domain
  q_injective := injective_on a.challenges.eta
  point_injective := NNG_LIBData.point_injective
  publicError := rfl
  terminalError := rfl
  equalError := rfl
  at28 := NNG_LIBArrays.at28 a.challenges.eta
  bytes_length := NNG_LIBData.bytes_length
  root_bytes := NNG_LIBData.root_bytes

/-- Observer identities are operationally irrelevant by the arbitrary-obs
CLOSED mark law. Preserve the Option shape in this emitted representative. -/
def observer (obs : RSL.Observer) : NNG_Emitted.Observer :=
  obs.map (fun _ => fun _ => .ok ())

def input (a : Args) (obs : RSL.Observer) (env : RSL.Env) : Parent Unit Unit :=
  NNG_ConcreteInput136.input a.public_ a.prefix_ a.transcript a.challenges (observer obs) env

def calls (_ : Args) (env : RSL.Env) : Calls := NNG_ConcreteCalls136.calls env
def events (_ : Args) : RSL.Env → NMT_CallTree.Event → List RSL.Event := NNG_LIBEvents136.events

def producer : Args → RSL.Observer → RSL.Env → RSL.Obs (Except VL.WErr (RSL.Verified VL)) :=
  NNG_DEnvObserved136.producer VL project calls input events

theorem inputs (a : Args) (obs : RSL.Observer) (env : RSL.Env) : Inputs VL (project a) a (input a obs env) :=
  ⟨project_lower_challenges a.challenges.eta a.challenges,
    eta_input a.challenges.eta a.challenges,NNG_LIBData.c1Root a.prefix_⟩
#print axioms inputs
end AspisR1.NNG_Representation136
