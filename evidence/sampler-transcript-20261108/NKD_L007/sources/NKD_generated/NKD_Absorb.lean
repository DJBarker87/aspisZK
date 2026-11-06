import NGT_EmittedEq
import NGT_NBA_Transcript
set_option autoImplicit false
namespace AspisR1.NKD_Absorb
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Total source-ordered cut: checked tag arithmetic precedes the exact four slices. -/
def G {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) : Result (transcript.Transcript H) := do
 let tag ← 160#u8 + row
 let reply ← D.digest before.hash (NGT_NBA_Transcript.absorbParts before.state tag payload)
 ok {before with state := reply}
/-- TX1:165: all Result arms; no digest reply or caller success premise. -/
theorem root {H : Type} (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) :
 transcript.Transcript.absorb D before row payload = G D before row payload := by
 simp only [transcript.Transcript.absorb,G,NGT_NBA_Transcript.absorbParts,lift,bind_tc_ok]
#print root
#print axioms root
end AspisR1.NKD_Absorb
