import AuS1_Suffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Absorb
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

 def parts (state : Array U8 32#usize) (tag : U8) (len : U32) (payload : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8,tag]),
    Array.to_slice (core.num.U32.to_le_bytes len),payload])

 theorem code {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row tag : U8) (payload : Slice U8) (len : U32)
    (tag_eq : 160#u8 + row = ok tag)
    (len_eq : UScalar.cast .U32 (Slice.len payload) = ok len) :
    PreparedHashEffects.absorb effects D self row payload =
      (do let state ← effects.digest D self.hash (parts self.state tag len payload)
          pure {self with state}) := by
  unfold PreparedHashEffects.absorb parts
  simp only [tag_eq,len_eq]
  rfl

 theorem read {H : Type} (D : aspis_core.Digest32 H) (self after : transcript.Transcript H)
    (row tag : U8) (payload : Slice U8) (len : U32)
    (tag_eq : 160#u8 + row = ok tag)
    (len_eq : UScalar.cast .U32 (Slice.len payload) = ok len)
    (success : erase (PreparedHashEffects.absorb effects D self row payload) = ok after) :
    Read (observe (run (PreparedHashEffects.absorb effects D self row payload)).1)
      (flatten (parts self.state tag len payload)) := by
  rw [code D self row tag payload len tag_eq len_eq] at success ⊢
  rw [erase_bind,erase_digest] at success
  cases call : D.digest self.hash (parts self.state tag len payload) with
  | fail e => simp only [call,bind_tc_fail] at success; cases success
  | div => simp only [call,bind_tc_div] at success; cases success
  | ok state =>
    change Read (observe (run (Code.digest D self.hash (parts self.state tag len payload)
      (fun a => .done {self with state := a}))).1) _
    simp only [run,call,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append]
    exact List.mem_singleton_self _

#print axioms code
#print axioms read
end AspisR1.AuS1_Absorb
end
