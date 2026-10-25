import AuS1_Absorb
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Block
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Suffix

 theorem read {H : Type} (D : aspis_core.Digest32 H) (self after : transcript.Transcript H)
    (row tag : U8) (payload : Slice U8) (len : U32) (block : Array U8 32#usize)
    (tag_eq : 160#u8 + row = ok tag)
    (len_eq : UScalar.cast .U32 (Slice.len payload) = len)
    (success : erase (PreparedHashEffects.block effects D self row payload) = ok (block,after)) :
    Read (observe (run (PreparedHashEffects.block effects D self row payload)).1)
      (flatten (AuS1_Absorb.parts self.state tag len payload)) := by
  unfold PreparedHashEffects.block at success ⊢
  obtain ⟨a,ha,hk,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  exact left_read _ _ _ success _ (AuS1_Absorb.read D self a row tag payload len tag_eq len_eq ha)

 theorem scalar_read (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
    (len : U32) (nz : Bool) (value : aspis_core.field.WideExact)
    (tag_eq : 160#u8 + row = ok tag)
    (len_eq : UScalar.cast .U32 (Slice.len payload) = len)
    (success : erase (PreparedScalarEffects.scalar effects B D self row payload nz) = ok (value,after)) :
    Read (observe (run (PreparedScalarEffects.scalar effects B D self row payload nz)).1)
      (flatten (AuS1_Absorb.parts self.state tag len payload)) := by
  unfold PreparedScalarEffects.scalar at success ⊢
  obtain ⟨a,ha,hk,logs⟩ := AuS1_Trace.success_bind _ _ _ success
  exact left_read _ _ _ success _ (read D self a.2 row tag payload len a.1 tag_eq len_eq ha)

#print axioms read
#print axioms scalar_read
end AspisR1.AuS1_Block
end
