import NGT_NBA_Transcript
set_option autoImplicit false
namespace AspisR1.NKD_New
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
/-- Deployed private-leaf-salts domain, exact variant tag and SAME semantic bytes. -/
def parts (semantic : Bytes32) (tag : U8) : Slice (Slice U8) :=
 Array.to_slice (Array.make 3#usize [Array.to_slice NGT_NBA_Transcript.domain,
 Array.to_slice (Array.make 1#usize [tag]),Array.to_slice semantic])
def G {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (semantic : Bytes32) (variant : transport.Variant) : Result (transcript.Transcript H) := do
 let tag ← transport.Variant.tag variant
 let reply ← D.digest hash (parts semantic tag)
 ok ⟨reply,hash⟩
/-- TX1:167: every variant and every digest outcome; hash carrier is retained. -/
theorem root {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (semantic : Bytes32) (variant : transport.Variant) :
 transcript.Transcript.new D hash semantic variant = G D hash semantic variant := by
 cases variant <;> simp only [transcript.Transcript.new,G,parts,
 NGT_NBA_Transcript.domain,transport.Variant.tag,lift,bind_tc_ok]
#print root
#print axioms root
end AspisR1.NKD_New
