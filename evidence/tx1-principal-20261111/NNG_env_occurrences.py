from pathlib import Path
import runpy
E=Path(__file__).resolve().parent
old=E/'NNG_EmittedOccurrences136.lean';before=old.read_bytes()
data=runpy.run_path(str(E/'NNG_emitted_occurrences.py'))
assert old.read_bytes()==before, 'Do not mutate the earlier compiled interface'
fx,pure=data['fx'],data['pure'];Event=data['Event']
s='''import NNG_EnvCallGraph136
set_option autoImplicit false
namespace AspisR1.NNG_EnvOccurrences136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
open NNG_Observed136 NNG_EmittedCallGraph
'''
for site,field,rawargs,semargs,arg,rawarg,raw,ret,semret in fx:
 s+=f'''\n/-- SAME emitted {site} call at the actual environment. The field and call
must be graphs of the SAME CLOSED deterministic model at this Env. -/
theorem {site} (VL : RSL.VLib) (c : NNG_Emitted.Calls) {rawargs}
    {semargs} (decode : ({ret}) → {semret})
    (events : {Event}) (env : RSL.Env) (model : RSL.Obs ({semret}))
    (hd : VL.{field}.dom {arg})
    (source : (⟨exit decode ({raw}),
      events env (.call "{site}" {rawarg} ({raw}))⟩ : RSL.Obs ({semret})) = model)
    (fieldGraph : ∀ o, VL.{field}.law {arg} env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events "{site}" {rawarg} ({raw})) env =
      VL.{field}.run {arg} env :=
  NNG_EnvCallGraph136.effect_at VL.{field} {arg} hd decode events "{site}" {rawarg}
    ({raw}) env model source fieldGraph
#print axioms {site}
'''
for site,field,rawargs,semargs,arg,rawarg,raw,ret,semret in pure:
 s+=f'''\n/-- Actual emitted {site}: exact returned value (inner Err included), with
silence proved at the same environment. This is an occurrence law, not a
VLib field instance or a final root premise. -/
theorem {site} (VL : RSL.VLib) (c : NNG_Emitted.Calls) {rawargs}
    {semargs} (decode : ({ret}) → {semret}) (events : {Event}) (env : RSL.Env) (model : {semret})
    (source : resultMap decode ({raw}) = .ok model)
    (fieldGraph : VL.{field} {arg} = model)
    (silent : events env (.call "{site}" {rawarg} ({raw})) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events "{site}" {rawarg} ({raw})) env =
      (RSL.Spec.pure (VL.{field} {arg})) env :=
  NNG_EnvCallGraph136.pure_at decode events "{site}" {rawarg} ({raw}) env model
    (VL.{field} {arg}) source fieldGraph silent
#print axioms {site}
'''
s+='end AspisR1.NNG_EnvOccurrences136\n'
(E/'NNG_EnvOccurrences136.lean').write_text(s)
