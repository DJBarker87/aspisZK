import NNH_ReturnedRE
import LIB_Instances
set_option autoImplicit false
noncomputable section
namespace NNH_FinishReturns
open RSL NND_Returned NNH_ReturnedRE
attribute [local instance] Classical.propDecidable
abbrev V := LIB_Instances.VL

def value (a : TX1_136.Args V) (env : Env) : Except V.WErr (Verified V) :=
 bindValue (LIB_VLib.semanticRoundsValue (a.prefix_,a.transcript) env) fun r =>
 let running := r.1
 let alpha := r.2.1
 let t1 := r.2.2
 bindValue (LIB_VLib.claimsValue a.prefix_ env) fun claims =>
 let orig := V.origChallenges a.challenges
 bindValue (RE.mapE (fun _ => V.wPublic) (LIB_VLib.terminalQm31Value (a.public_,claims,alpha,orig) env)) fun terminal =>
 let mask := V.maskValue claims alpha
 bindValue (V.validatedRecord a.prefix_ 25) fun rec25 =>
 bindValue (V.decodeK29 rec25 87) fun extra =>
 let masked := V.qadd (V.qadd mask (V.qmul (V.eta a.challenges) terminal)) (V.at28 extra)
 bindValue (if decide (running ≠ masked) then .error V.wTerminal else .ok ()) fun _ =>
 let stateBefore := V.state t1
 bindValue (V.validatedRecord a.prefix_ 25) fun rec25' =>
 bindValue (LIB_VLib.circleValue (t1,rec25') env) fun c0 =>
 let z0 := c0.1
 let t2 := c0.2
 bindValue (V.validatedRecord a.prefix_ 26) fun rec26 =>
 bindValue (V.decodeK29 rec26 0) fun beforeZ1 =>
 bindValue (V.validatedRecord a.prefix_ 26) fun rec26' =>
 bindValue (LIB_VLib.circleValue (t2,rec26') env) fun c1 =>
 let z1 := c1.1
 let t3 := c1.2
 bindValue (if decide (z0 = z1) then .error V.wEqualCirclePoints else .ok ()) fun _ =>
 bindValue (V.payload a.prefix_ 2) fun p2 =>
 match TX1_136.toB32 p2 with
 | none => .error V.wPublic
 | some root1 => .ok ⟨(V.c1Root a.prefix_,root1),a.challenges,alpha,claims,extra,
   beforeZ1,stateBefore,(z0,z1),t3⟩

theorem returned (a : TX1_136.Args V) (env : Env) :
 Returns (TX1_136.Ref V a) env (value a env) := by
 unfold TX1_136.Ref value
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.semanticRounds_returns _ env))
 intro r
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.claims_returns _ env))
 intro claims
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.mapErr _ _ env _ (child _ _ env _ (LIB_VLib.terminalQm31_returns _ env)))
 intro terminal
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro rec25
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro extra
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.check env _ _)
 intro _
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro rec25'
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.circle_returns _ env))
 intro c0
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro rec26
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro beforeZ1
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro rec26'
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.circle_returns _ env))
 intro c1
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.check env _ _)
 intro _
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.ofExcept env _)
 intro p2
 split
 · exact NND_Returned.panic env _
 · exact NNH_ReturnedRE.pure env _

#print axioms returned
end NNH_FinishReturns
