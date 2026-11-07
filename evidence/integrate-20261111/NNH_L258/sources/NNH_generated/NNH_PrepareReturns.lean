import NNH_ObservedReturns
set_option autoImplicit false
noncomputable section
namespace NNH_PrepareReturns
open RSL NND_Returned NNH_ReturnedRE
abbrev V := LIB_Instances.VL
abbrev P := LIB_Instances.P

def frontValue (a : TX1_087.Args V) (env : Env) : Except V.VErr (Verified V × V.View) :=
 bindValue (RE.mapE (fun _ => V.vAllocation) (LIB_VLib.filledValue (LOGICAL_SEMANTIC+LOGICAL_Y1) env)) fun logical =>
 let semantic0 := logical.take LOGICAL_SEMANTIC
 let y10 := logical.drop LOGICAL_SEMANTIC
 bindValue (RE.mapE V.codecToV (LIB_VLib.expandSemanticValue (slice a.proof OFF_SEMANTIC OFF_Y1,semantic0) env)) fun semantic =>
 bindValue (RE.mapE V.codecToV (LIB_VLib.expandValuesValue (slice a.proof OFF_Y1 OFF_INACTIVE,y10) env)) fun y1 =>
 bindValue (LIB_VLib.wideViewValue (a.proof,semantic,y1) env) fun v =>
 bindValue (RE.mapE (fun _ => V.vSemantic) (NNH_ObservedReturns.value ⟨a.public_,V.viewSemantic v⟩ env)) fun sem =>
 .ok (sem,v)

def value (a : TX1_087.Args V) (env : Env) : Except V.VErr V.Prepared × V.E29 :=
 match frontValue a env with
 | .error e => (.error e,a.g)
 | .ok (sem,v) => LIB_Prepared.value (sem,v,a.g) env

theorem front_returned (a : TX1_087.Args V) (env : Env) :
 Returns (TX1_087.front V a) env (frontValue a env) := by
 unfold TX1_087.front frontValue
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.mapErr _ _ env _ (child _ _ env _ (LIB_VLib.filled_returns _ env)))
 intro logical
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.mapErr _ _ env _ (child _ _ env _ (LIB_VLib.expandSemantic_returns _ env)))
 intro semantic
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.mapErr _ _ env _ (child _ _ env _ (LIB_VLib.expandValues_returns _ env)))
 intro y1
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.wideView_returns _ env))
 intro v
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.mapErr _ _ env _ (NND_Returned.call_domain _ _ _ env _ (fun _ => NNH_ObservedReturns.returned _ env)))
 intro sem
 exact NNH_ReturnedRE.pure env _

theorem returned (a : TX1_087.Args V) (env : Env) :
 Returns (TX1_087.Ref V P a) env (value a env) := by
 unfold TX1_087.Ref value
 apply NND_Returned.bind _ _ env _ _ (front_returned a env)
 cases frontValue a env with
 | error e => exact NND_Returned.pure env _
 | ok pair =>
  exact NND_Returned.call_domain _ _ _ env _ (fun _ => LIB_Prepared.returns _ env)

#print axioms front_returned
#print axioms returned
end NNH_PrepareReturns
