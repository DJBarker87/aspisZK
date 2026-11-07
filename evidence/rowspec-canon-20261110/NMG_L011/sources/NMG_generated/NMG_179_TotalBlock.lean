import NGT_NBL_BlockTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMG_179_TotalBlock
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Conditional construction from primitive runtime totality, never from a
chosen successful Block. The runtime law must be installed at this SAME digest. -/
theorem construct {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
 (tagCall : (160#u8+row : Result U8)=ok tag)
 (total : ∀ parts, ∃ out, D.digest before.hash parts=ok out) :
 Nonempty (NGT_NBL_BlockTrace.Block D before row payload) := by
 obtain ⟨absorbed,absorbCall⟩ := total (NGT_NBA_Transcript.absorbParts before.state tag payload)
 obtain ⟨value,readCall⟩ := total (NGT_NBA_Transcript.readParts absorbed 1#u8)
 obtain ⟨final,advanceCall⟩ := total (NGT_NBA_Transcript.readParts absorbed 2#u8)
 exact ⟨⟨tag,tagCall,absorbed,value,final,absorbCall,readCall,advanceCall⟩⟩
#print axioms construct
end AspisR1.NMG_179_TotalBlock
end
