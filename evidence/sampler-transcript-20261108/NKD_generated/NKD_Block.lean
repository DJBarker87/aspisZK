import NKD_Absorb
set_option autoImplicit false
namespace AspisR1.NKD_Block
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Both suffix queries use the absorbed state, in read/advance order. -/
def G {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) : Result ((Array U8 32#usize) × transcript.Transcript H) := do
 let absorbed ← NKD_Absorb.G D before row payload
 let value ← D.digest absorbed.hash (NGT_NBA_Transcript.readParts absorbed.state 1#u8)
 let final ← D.digest absorbed.hash (NGT_NBA_Transcript.readParts absorbed.state 2#u8)
 ok (value,{absorbed with state := final})
/-- TX1:166: discharge the absorb child internally, retaining errors/abort prefixes. -/
theorem root {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) :
 transcript.Transcript.block D before row payload = G D before row payload := by
 unfold transcript.Transcript.block G
 rw [NKD_Absorb.root]
 simp only [NGT_NBA_Transcript.readParts,lift,bind_tc_ok]
#print root
#print axioms root
end AspisR1.NKD_Block
