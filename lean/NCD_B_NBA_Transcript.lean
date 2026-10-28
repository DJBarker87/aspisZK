-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBA_Installed
set_option autoImplicit false
namespace AspisR1.NBA_Transcript
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize

def absorbParts (state : Bytes32) (tag : U8) (payload : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,tag]),
    Array.to_slice (core.num.U32.to_le_bytes (UScalar.cast .U32 (Slice.len payload))),payload])

def readParts (state : Bytes32) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [Array.to_slice state,
    Array.to_slice (Array.make 1#usize [tag])])

theorem absorb {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row tag : U8) (payload : Slice U8) (state : Bytes32)
    (htag : (160#u8+row : Result U8)=ok tag)
    (call : D.digest before.hash (absorbParts before.state tag payload)=ok state) :
    transcript.Transcript.absorb D before row payload=ok {before with state:=state} := by
  unfold transcript.Transcript.absorb
  simp only [lift,bind_tc_ok,htag,absorbParts] at call ⊢
  rw [call,bind_tc_ok]

theorem block {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
    (row tag : U8) (payload : Slice U8) (absorbed value final : Bytes32)
    (htag : (160#u8+row : Result U8)=ok tag)
    (first : D.digest before.hash (absorbParts before.state tag payload)=ok absorbed)
    (second : D.digest before.hash (readParts absorbed 1#u8)=ok value)
    (third : D.digest before.hash (readParts absorbed 2#u8)=ok final) :
    transcript.Transcript.block D before row payload=ok (value,{before with state:=final}) := by
  have start := absorb D before row tag payload absorbed htag first
  unfold transcript.Transcript.block
  rw [start,bind_tc_ok]
  simp only [lift,bind_tc_ok,readParts] at second third ⊢
  rw [second,bind_tc_ok,third,bind_tc_ok]

def domain : Array U8 29#usize := Array.make 29#usize [
    85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,
    49#u8,58#u8,80#u8,82#u8,73#u8,86#u8,65#u8,84#u8,69#u8,45#u8,
    83#u8,65#u8,76#u8,84#u8,69#u8,68#u8,58#u8,80#u8,51#u8]

def seedParts (state : Bytes32) : Slice (Slice U8) := Array.to_slice
  (Array.make 3#usize [Array.to_slice domain,
    Array.to_slice (Array.make 1#usize [2#u8]),Array.to_slice state])

theorem seed {H : Type} (D : aspis_core.Digest32 H) (hash : H) (state reply : Bytes32)
    (call : D.digest hash (seedParts state)=ok reply) :
    transcript.Transcript.new D hash state .S2=ok (⟨reply,hash⟩ : transcript.Transcript H) := by
  unfold transcript.Transcript.new
  simp only [transport.Variant.tag,lift,bind_tc_ok,seedParts,domain] at call ⊢
  rw [call,bind_tc_ok]

#print axioms seed
#print axioms absorb
#print axioms block
end AspisR1.NBA_Transcript
