import NNH_PrepareReturns
import NNH_Tx1ReturnedValues
set_option autoImplicit false
noncomputable section
namespace NNH_Tx1Returns
open RSL NND_Returned NNH_ReturnedRE
abbrev V := LIB_Instances.VL
abbrev P := LIB_Instances.P

def preparedValue (a : TX1_087.Args V) (env : Env) : Except V.VErr (V.Prepared × V.E29) :=
 let r := NNH_PrepareReturns.value a env
 match r.1 with | .error e => .error e | .ok p => .ok (p,r.2)

theorem prepared_returned (a : TX1_087.Args V) (env : Env) :
 Returns (Spec.bind (Spec.call (fun x : TX1_087.Args V => TX1_087.Domain V x none)
 (TX1_087.Ref V P) a) (fun r => match r.1 with
 | .ok p => Spec.pure (.ok (p,r.2)) | .error e => Spec.pure (.error e))) env
 (preparedValue a env) := by
 apply NND_Returned.bind _ _ env _ _
  (NND_Returned.call_domain _ _ _ env _ (fun _ => NNH_PrepareReturns.returned a env))
 unfold preparedValue
 cases NNH_PrepareReturns.value a env with
 | mk r g => cases r <;> exact NND_Returned.pure env _

def value (a : TX1_094.Args V) (env : Env) : Except V.VErr Bytes :=
 bindValue (if a.k != SPLIT then .error V.vParse else .ok ()) fun _ =>
 bindValue (LIB_VLib.parseShapeValue a.proof env) fun _ =>
 bindValue (LIB_VLib.canonicalScanValue a.proof env) fun _ =>
 bindValue (preparedValue ⟨a.public_,a.proof,V.zeroE29⟩ env) fun pg =>
 let p := pg.1
 let g := pg.2
 bindValue (LIB_VLib.accNewValue () env) fun acc =>
 match TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) with
 | none => .error V.vParse
 | some folded =>
  bindValue (LIB_VLib.batchMerkleValue (a.proof,p,folded,0) env) fun _ =>
  bindValue (LIB_VLib.geometryValue (p,0,a.k) env) fun geo =>
  bindValue (LIB_VLib.weightsNewValue acc env) fun pending =>
  bindValue (LIB_VLib.queryLoopValue (a.proof,p,acc,g,geo,pending,a.k) env) fun r =>
  bindValue (.ok (LIB_VLib.finishValue (r.2,r.1) env)) fun acc2 =>
  bindValue (.ok (LIB_VLib.checkpointValue (p,acc2,a.proof,a.public_bytes) env)) fun bytes =>
  .ok bytes

theorem returned (a : TX1_094.Args V) (env : Env) :
 Returns (TX1_094.Ref V P a) env (value a env) := by
 unfold TX1_094.Ref value RE.seq
 apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.check env _ _)
 intro _
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.parseShape_returns _ env))
 intro _
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.canonicalScan_returns _ env))
 intro _
 apply NNH_ReturnedRE.bind _ _ env _ _ (prepared_returned _ env)
 intro pg
 apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.accNew_returns _ env))
 intro acc
 split
 · exact NND_Returned.panic env _
 · apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.batchMerkle_returns _ env))
   intro _
   apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.geometry_returns _ env))
   intro geo
   apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.weightsNew_returns _ env))
   intro pending
   apply NNH_ReturnedRE.bind _ _ env _ _ (child _ _ env _ (LIB_VLib.queryLoop_returns _ env))
   intro r
   apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.lift _ env _ (NND_Returned.call_domain _ _ _ env _ (fun _ => LIB_VLib.finish_returns _ env)))
   intro acc2
   apply NNH_ReturnedRE.bind _ _ env _ _ (NNH_ReturnedRE.lift _ env _ (NND_Returned.call_domain _ _ _ env _ (fun _ => LIB_VLib.checkpoint_returns _ env)))
   intro bytes
   exact NNH_ReturnedRE.pure env bytes

/-- Full concrete TX1 evaluator input of the existing345 Returns composer. -/
def values : NNH_Tx1ReturnedValues.Values V P := ⟨value,returned⟩
#print axioms prepared_returned
#print axioms returned
#print axioms values
end NNH_Tx1Returns
