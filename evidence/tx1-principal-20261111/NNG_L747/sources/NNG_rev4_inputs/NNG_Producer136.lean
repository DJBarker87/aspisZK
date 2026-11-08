import NNG_Representation136
import NNG_FinalEvents136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Producer136
open NNG_Representation136

def events (_ : Args) : RSL.Env → NMT_CallTree.Event → List RSL.Event := NNG_FinalEvents136.events

def producer : Args → RSL.Observer → RSL.Env → RSL.Obs (Except VL.WErr (RSL.Verified VL)) :=
  NNG_DEnvObserved136.producer VL project calls input events
end AspisR1.NNG_Producer136
