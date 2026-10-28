import NCB_DigestTotal
import NBR_BlockConstruct
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCB_ChronologicalBlock
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- Instantiate the existing block constructor at the adopted TOTAL oracle
completion. Native request validity and chronological observation are separate. -/
theorem construct {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (before : transcript.Transcript Hash) (row : U8) (payload : Slice U8) (bound : row.val≤95) :
    Nonempty (NBL_BlockTrace.Block (F3U_Rehash.dictionary H D) before row payload) :=
  NBR_BlockConstruct.block _ (fun hash parts => NCB_DigestTotal.total H D hash parts)
    before row payload bound

/-- Three reached native replies, at the SAME causal request slices, build
one chronological model Block. Digest VALUES are precisely the runtime SHA row;
no successful whole model/native block result is an input. -/
theorem observed {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (before : transcript.Transcript Hash) (row tag : U8) (payload : Slice U8)
    (tagCall : 160#u8+row=ok tag)
    (absorbed value final : Array U8 32#usize)
    (absorbRuntime : decodeState absorbed=H (flatten (NBA_Transcript.absorbParts before.state tag payload)))
    (readRuntime : decodeState value=H (flatten (NBA_Transcript.readParts absorbed 1#u8)))
    (advanceRuntime : decodeState final=H (flatten (NBA_Transcript.readParts absorbed 2#u8))) :
    ∃ b : NBL_BlockTrace.Block (F3U_Rehash.dictionary H D) before row payload,
      b.absorbed=absorbed ∧ b.value=value ∧ b.final=final ∧
      transcript.Transcript.block (F3U_Rehash.dictionary H D) before row payload=
        ok (value,{before with state:=final}) := by
  let b : NBL_BlockTrace.Block (F3U_Rehash.dictionary H D) before row payload :=
    ⟨tag,tagCall,absorbed,value,final,
      NCB_DigestTotal.reached H D before.hash _ absorbed absorbRuntime,
      NCB_DigestTotal.reached H D before.hash _ value readRuntime,
      NCB_DigestTotal.reached H D before.hash _ final advanceRuntime⟩
  exact ⟨b,rfl,rfl,rfl,NBL_BlockTrace.block_result _ before row payload b⟩
#print axioms construct
#print axioms observed
end AspisR1.NCB_ChronologicalBlock
end
