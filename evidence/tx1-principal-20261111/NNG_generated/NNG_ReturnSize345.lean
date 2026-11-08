import NNG_ReturnedRef094
import NNG_Candidate328
import NNG_Error328
import LIBC_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReturnSize345
open Aeneas Aeneas.Std Result RSL NNG_ReturnedRef094

theorem writer (p : AspisR1.CheckpointBytes5Writer.Prepared)
 (a : AspisR1.CheckpointBytes5Writer.Accumulator)
 (hp hu hc : AspisR1.CheckpointBytes5Effect.Digest) :
 (AspisR1.CheckpointBytes5Writer.finish p a hp hu hc).val.length=1768 := by
 change ((AspisR1.CheckpointBytesDecodeC5.sourceBody p a hp hu).map AspisR1.CheckpointBytes5Writer.u8 ++ hc.val).length=1768
 rw [List.length_append,List.length_map]
 have body : (AspisR1.CheckpointBytesDecodeC5.sourceBody p a hp hu).length=1736 := by
  simp only [AspisR1.CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
 have checksum : hc.val.length=32 := hc.property
 rw [body,checksum]
#print axioms writer

theorem value (a : LIBC_Checkpoint.Args) (env : Env) : (LIBC_Checkpoint.value a env).length=1768 := by
 unfold LIBC_Checkpoint.value
 rw [NMS_R2N_RSLScalars.bytes_length]
 exact writer _ _ _ _ _
#print axioms value

theorem checkpoint (a : LIBC_Checkpoint.Args) (env : Env) (out : Bytes) (ev : List Event)
 (h : LIB_Instances.VL.checkpoint.run a env ⟨.ret out,ev⟩) : out.length=1768 := by
 have same := (LIBC_Checkpoint.returns a env) _ _ h.2 rfl
 rw [same]
 exact value a env
#print axioms checkpoint

theorem tx1 (a : TX1_094.Args LIB_Instances.VL) (env : Env) (out : Bytes) (ev : List Event)
 (h : TX1_094.Ref LIB_Instances.VL LIB_Instances.P a env ⟨.ret (.ok out),ev⟩) :
 out.length=1768 := by
 unfold TX1_094.Ref at h
 obtain ⟨_,_,_,_,h⟩:=bind_ok h
 obtain ⟨_,_,_,_,h⟩:=bind_ok h
 obtain ⟨_,_,_,_,h⟩:=bind_ok h
 obtain ⟨pg,_,_,_,h⟩:=bind_ok h
 obtain ⟨acc,_,_,_,h⟩:=bind_ok h
 cases folded : TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) with
 | none=>
  rw [folded] at h
  obtain ⟨_,impossible⟩:=lift_ok h
  cases congrArg Obs.exit impossible
 | some root=>
  rw [folded] at h
  obtain ⟨_,_,_,_,h⟩:=bind_ok h
  obtain ⟨_,_,_,_,h⟩:=bind_ok h
  obtain ⟨_,_,_,_,h⟩:=bind_ok h
  obtain ⟨_,_,_,_,h⟩:=bind_ok h
  obtain ⟨_,_,_,_,h⟩:=bind_ok h
  obtain ⟨bytes,_,_,hc,tail⟩:=bind_ok h
  have same : out=bytes := Except.ok.inj (Exit.ret.inj (congrArg Obs.exit tail))
  rw [same]
  obtain ⟨es,hc⟩:=lift_ok hc
  exact checkpoint _ env bytes es hc
#print axioms tx1

theorem first (a : TX1_328.Args LIB_Instances.VL) (env : Env) (out : Bytes) (ev : List Event)
 (h : TX1_328.Ref LIB_Instances.VL LIB_Instances.P a env ⟨.ret (.ok out),ev⟩) :
 out.length=1768 := by
 unfold TX1_328.Ref at h
 obtain ⟨r,e1,e2,child,tail⟩:=bind_ret h
 cases r with
 | ok bytes=>
  have same : out=bytes := Except.ok.inj (Exit.ret.inj (congrArg Obs.exit tail))
  rw [same]
  exact tx1 a env bytes e1 child.2
 | error e=>
  have errorLaw := NNG_Error328.target_iff (NNG_Carriers328.errorBack e) env ⟨.ret (.ok out),e2⟩
  rw [NNG_Carriers328.error_back] at errorLaw
  rcases errorLaw.mp tail with same|same <;> cases congrArg Obs.exit same
#print axioms first

theorem producer (a : TX1_328.Args LIB_Instances.VL) (env : Env)
 (dom : TX1_328.Domain LIB_Instances.VL a) (out : Bytes) (ev : List Event)
 (returned : NNG_Producer328.producer a env=⟨.ret (.ok out),ev⟩) : out.length=1768 := by
 have h := NNG_Candidate328.candidate a env dom
 rw [returned] at h
 exact first a env out ev h
#print axioms producer
end AspisR1.NNG_ReturnSize345
