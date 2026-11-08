import NNH_FinishReturns
set_option autoImplicit false
noncomputable section
namespace NNH_ObservedReturns
open RSL NND_Returned NNH_ReturnedRE
abbrev V := LIB_Instances.VL

def value (a : TX1_137.Args V) (env : Env) : Except V.WErr (Verified V) :=
 bindValue (LIB_VLib.parsePrefixValue a.bytes env) fun pfx =>
 bindValue (LIB_VLib.publicTranscriptValue (a.public_,V.c1Root pfx) env) fun t0 =>
 bindValue (LIB_VLib.beginValue (pfx,t0) env) fun r =>
 NNH_FinishReturns.value ⟨a.public_,pfx,r.2,r.1⟩ env

theorem returned (a : TX1_137.Args V) (env : Env) :
 Returns (TX1_137.Ref V a) env (value a env) := by
 unfold TX1_137.Ref value
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.parsePrefix_returns _ env))
 intro pfx
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.publicTranscript_returns _ env))
 intro t0
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.begin_returns _ env))
 intro r
 exact NND_Returned.call_domain _ _ _ env _ (fun _ => NNH_FinishReturns.returned _ env)

#print axioms returned
end NNH_ObservedReturns
