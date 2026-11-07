import NNG_Reference094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReferenceMatch094
open RSL Aeneas Aeneas.Std NNG_Carriers094
abbrev Args := NNG_Input094.Args

def original (a : Args) : RE LIB_VCarriers.VErr Bytes :=
 let V:=LIB_Instances.VL
 let P:=LIB_Instances.P
  RE.bind (Spec.bind (Spec.call (fun x : TX1_087.Args V => TX1_087.Domain V x none)
                (TX1_087.Ref V P) ⟨a.public_, a.proof, V.zeroE29⟩)
            (fun r => match r.1 with
              | .ok p => Spec.pure (.ok (p, r.2))
              | .error e => Spec.pure (.error e))) fun pg =>
  let p := pg.1
  let g := pg.2
  RE.bind (V.accNew.run ()) fun acc =>
  -- mark(obs, Prepare): no effect
  match TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) with
  | none => RE.lift Spec.panic
  | some folded =>
  RE.seq (V.batchMerkle.run (a.proof, p, folded, 0)) <|
  -- mark(obs, Merkle(0)): no effect
  RE.bind (V.geometry.run (p, 0, a.k)) fun geo =>
  RE.bind (V.weightsNew.run acc) fun pending =>
  RE.bind (V.queryLoop.run (a.proof, p, acc, g, geo, pending, a.k)) fun r =>
  RE.bind (RE.lift (V.finish.run (r.2, r.1))) fun acc2 =>
  RE.bind (RE.lift (V.checkpoint.run (p, acc2, a.proof, a.public_bytes))) fun bytes =>
  -- mark(obs, CheckpointWrite): no effect
  RE.pure bytes

theorem same (a : Args) (obs : Observer) (env : Env)
 (own : TX1_094.Domain LIB_Instances.VL a obs a.public_) (split : a.k=10)
 (width : a.proof.length=57607) :
 NNG_Reference094.prepare (NNG_Input094.input a obs env)=original a := by
 have proofSame : LIB_Carriers.bytes (NNG_Input094.input a obs env).proof=a.proof :=
  LIBC_Bytes.to_native a.proof (by rw [width];scalar_tac)
 have publicSame : toT9 (NNG_Input094.input a obs env).publicValue=a.public_ := fromT9_inverse _
 have publicBytesSame := NNG_Input094.public_extent a obs env own
 unfold NNG_Reference094.prepare NNG_Reference094.afterPrepare NNG_Reference094.afterNew
  NNG_Reference094.batch NNG_Reference094.geometry NNG_Reference094.weights NNG_Reference094.query
  NNG_Reference094.finish NNG_Reference094.checkpoint original
 rw [proofSame,publicSame,publicBytesSame,split]
 rfl
#print axioms same
end AspisR1.NNG_ReferenceMatch094
