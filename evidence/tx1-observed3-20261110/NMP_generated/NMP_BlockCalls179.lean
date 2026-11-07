import NGT_NBL_BlockTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_BlockCalls179
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Narrow utility only: the three actual primitive call equations, rather
than totality for every conceivable parts array. This is NOT a caller root;
the runtime law at these exact readable slices still has to supply the equations. -/
theorem construct {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
 (absorbed value final : Array U8 32#usize)
 (tagCall : (160#u8+row : Result U8)=ok tag)
 (absorbCall : D.digest before.hash (NGT_NBA_Transcript.absorbParts before.state tag payload)=ok absorbed)
 (readCall : D.digest before.hash (NGT_NBA_Transcript.readParts absorbed 1#u8)=ok value)
 (advanceCall : D.digest before.hash (NGT_NBA_Transcript.readParts absorbed 2#u8)=ok final) :
 Nonempty (NGT_NBL_BlockTrace.Block D before row payload) :=
 ⟨⟨tag,tagCall,absorbed,value,final,absorbCall,readCall,advanceCall⟩⟩
#print axioms construct
#print construct
end AspisR1.NMP_BlockCalls179
end
