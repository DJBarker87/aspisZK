import NNG_Input094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Reference094
open RSL Aeneas Aeneas.Std
abbrev V := LIB_Instances.VL
abbrev P := LIB_Instances.P
abbrev E := LIB_VCarriers.VErr
abbrev Source := NNG_Context094.Parent Unit
abbrev ResultSpec := RE E Bytes

def checkpoint (s : Source) (p : V.Prepared) (a : V.Acc) : ResultSpec :=
 RE.bind (RE.lift (V.checkpoint.run (p,a,LIB_Carriers.bytes s.proof,LIB_Carriers.bytes s.publicBytes))) RE.pure

def finish (s : Source) (p : V.Prepared) (r : V.Acc × V.Weights) : ResultSpec :=
 RE.bind (RE.lift (V.finish.run (r.2,r.1))) (checkpoint s p)

def query (s : Source) (p : V.Prepared) (g : V.E29) (a : V.Acc) (geo : V.Geo) (b : V.Weights) : ResultSpec :=
 RE.bind (V.queryLoop.run (LIB_Carriers.bytes s.proof,p,a,g,geo,b,10)) (finish s p)

def weights (s : Source) (p : V.Prepared) (g : V.E29) (a : V.Acc) (geo : V.Geo) : ResultSpec :=
 RE.bind (V.weightsNew.run a) (query s p g a geo)

def geometry (s : Source) (p : V.Prepared) (g : V.E29) (a : V.Acc) : ResultSpec :=
 RE.bind (V.geometry.run (p,0,10)) (weights s p g a)

def batch (s : Source) (p : V.Prepared) (g : V.E29) (a : V.Acc) (folded : B32) : ResultSpec :=
 RE.seq (V.batchMerkle.run (LIB_Carriers.bytes s.proof,p,folded,0)) (geometry s p g a)

def afterNew (s : Source) (p : V.Prepared) (g : V.E29) (a : V.Acc) : ResultSpec :=
 match TX1_136.toB32 (slice (LIB_Carriers.bytes s.proof) OFF_FOLDED_ROOT OFF_ROUND1) with
 | none=>RE.lift Spec.panic
 | some folded=>batch s p g a folded

def afterPrepare (s : Source) (pg : V.Prepared × V.E29) : ResultSpec :=
 RE.bind (V.accNew.run ()) (afterNew s pg.1 pg.2)

def normalized (r : Except V.VErr V.Prepared × V.E29) : Except V.VErr (V.Prepared × V.E29) :=
 match r.1 with | .ok p=>.ok (p,r.2) | .error e=>.error e

def prepare (s : Source) : ResultSpec :=
 RE.bind (Spec.map normalized
  (Spec.call (fun a : TX1_087.Args V=>TX1_087.Domain V a none) (TX1_087.Ref V P)
   ⟨NNG_Carriers094.toT9 s.publicValue,LIB_Carriers.bytes s.proof,V.zeroE29⟩)) (afterPrepare s)
end AspisR1.NNG_Reference094
