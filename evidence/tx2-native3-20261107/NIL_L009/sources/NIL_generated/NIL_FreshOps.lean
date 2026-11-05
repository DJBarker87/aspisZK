import NIL_StatePort
import NIL_ResultReverse
import NID_ResumeEmissionFuns
import NID_WeightReadsTransport
set_option autoImplicit false
noncomputable section
namespace NIL_FreshOps
open Aeneas Aeneas.Std Result NIL_Carriers
open AspisR1

def mapError {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
 (x : core.result.Result T E) (f : O) : Result (core.result.Result T F) :=
 match x with
 | .Ok v => ok (.Ok v)
 | .Err err => do let out ← inst.call_once f err;ok (.Err out)

def anyLoop {T F : Type} (inst : core.ops.function.FnMut F T Bool) :
 Nat → core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)
 | 0,it,_ => ok (false,it)
 | n+1,it,f => do
   let (value,rest) ← core.slice.iter.IteratorSliceIter.next it
   match value with
   | none => ok (false,rest)
   | some x =>
     let (b,f') ← inst.call_mut f x
     if b then ok (true,rest) else anyLoop inst n rest f'

def any {T F : Type} (inst : core.ops.function.FnMut F T Bool)
 (it : core.slice.iter.Iter T) (f : F) : Result (Bool × core.slice.iter.Iter T) :=
 anyLoop inst (it.slice.val.length+1) it f

def filled (reserved : Bool) {T : Type} (_ : core.marker.Copy T) (n : Usize) (x : T) :
 Result (core.result.Result (alloc.vec.Vec T) NID_ResumeEmission.aspis_core.r0.Error) :=
 if reserved then ok (.Ok ⟨List.replicate n.val x,by simp;scalar_tac⟩)
 else ok (.Err .Allocation)

def raw (N : Usize) (r : Fresh.R) : Result (Array U8 N × Fresh.R) :=
 outer (fun x=>(x.1,unReader x.2)) (CheckpointBytes3Reader.raw N (reader r))
def readK (r : Fresh.R) : Result (core.result.Result Fresh.K Fresh.Err × Fresh.R) :=
 outer (fun x=>(unInner unK x.1,unReader x.2)) (CheckpointBytes3Reader.readK (reader r))
def readE (r : Fresh.R) : Result (core.result.Result Fresh.E Fresh.Err × Fresh.R) :=
 outer (fun x=>(unInner unE x.1,unReader x.2)) (CheckpointBytes3Reader.readE (reader r))
def semantic (bytes : Slice U8) (start : Usize) :
 Result (core.result.Result (Array Fresh.K 10#usize × Usize) Fresh.Err) :=
 outer (unInner (fun x=>(array unK x.1,x.2))) (CheckpointBytes4Ops.readSemanticAlpha bytes start)
def weights (bytes : Slice U8) (start : Usize) (v : alloc.vec.Vec Fresh.K) :
 Result (core.result.Result (alloc.vec.Vec Fresh.K × Usize) Fresh.Err) :=
 outer (unInner (fun x=>(vec unK x.1,x.2))) (CheckpointBytes4Ops.readWeights bytes start (vec k v))
def validate (q : Array U32 22#usize) : Result (core.result.Result Unit Fresh.Err) :=
 outer (unInner id) (CheckpointBytes4Ops.validate q)
def digest {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) :
 NID_ResumeEmission.aspis_core.digest.Digest32 H := ⟨d.coremarkerCopyInst,d.digest⟩

def resume (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H) :=
 NID_ResumeEmission.verifier.resume
 CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq mapError any
 (fun x=>ok x) (ok (unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
 (filled reserved) semantic weights validate readK readE raw
 (fun v=>CheckpointBytes4Ops.checkpointSize (variant v))
 (fun v=>CheckpointBytes4Ops.finalLen (variant v))
 (fun v=>CheckpointBytes4Ops.tag (variant v)) (digest d) bytes proof public1 v hash

theorem raw_port (N : Usize) (r : Fresh.R) :
 outer (fun x=>(x.1,reader x.2)) (raw N r)=CheckpointBytes3Reader.raw N (reader r) := by
 unfold raw
 apply NIL_ResultTransport.outer_roundtrip
 intro x;cases x;simp only [reader_reverse]

theorem k_port (r : Fresh.R) :
 outer (fun x=>(NIL_Carriers.inner k x.1,reader x.2)) (readK r)=CheckpointBytes3Reader.readK (reader r) := by
 unfold readK
 apply NIL_ResultTransport.outer_roundtrip
 intro x;cases x
 simp only [NIL_ResultReverse.inner_reverse unK k k_reverse,reader_reverse]

theorem e_port (r : Fresh.R) :
 outer (fun x=>(NIL_Carriers.inner e x.1,reader x.2)) (readE r)=CheckpointBytes3Reader.readE (reader r) := by
 unfold readE
 apply NIL_ResultTransport.outer_roundtrip
 intro x;cases x
 simp only [NIL_ResultReverse.inner_reverse unE e e_reverse,reader_reverse]
#print axioms raw_port
#print axioms k_port
#print axioms e_port
end NIL_FreshOps
