import NNG_ReturnedRef094
import NNG_CheckpointExtent094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReturnedExtent094
open RSL NNG_ReturnedRef094
/-- A necessary condition imposed by the installed reference on any successful
returned transaction, despite its absence from Domain094. This does not
assert existence of a successful original transaction. -/
theorem required (a : TX1_094.Args LIB_Instances.VL) (env : Env) (out : Bytes) (ev : List Event)
 (h : TX1_094.Ref LIB_Instances.VL LIB_Instances.P a env ⟨.ret (.ok out),ev⟩) :
 a.public_bytes.length=1880 := by
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
  obtain ⟨_,_,_,checkpoint,_⟩:=bind_ok h
  obtain ⟨_,checkpoint⟩:=lift_ok checkpoint
  exact checkpoint.1.2.2
#print axioms required
end AspisR1.NNG_ReturnedExtent094
