import NGV_SemanticPacket
set_option autoImplicit false
noncomputable section
namespace LIBC_ExpandSemanticModel
open Aeneas Aeneas.Std Result
/-- Select a mathematical output interval, never a native execution witness. -/
def Row (j : Fin 13831) (late : ¬ j.val < 32) :
 {r : Nat // r < 27 ∧ NGD_SemanticSchedule.dst r ≤ j.val ∧
   j.val < NGD_SemanticSchedule.dst r + 5 + NFU_PacketDomains.payloadSize r} :=
 ⟨Classical.choose ((NGV_SemanticPacket.coverage j.val j.isLt).resolve_left late),
  Classical.choose_spec ((NGV_SemanticPacket.coverage j.val j.isLt).resolve_left late)⟩
def byte (input : Slice U8) (j : Fin 13831) : U8 :=
 if early : j.val < 32 then input.val[j.val]?.getD 0#u8
 else
  let r := (Row j early).val
  if j.val < NGD_SemanticSchedule.dst r + 5 then
   input.val[NGD_SemanticSchedule.src r + (j.val-NGD_SemanticSchedule.dst r)]?.getD 0#u8
  else NGV_SemanticValues.payloadByte input r (j.val-NGD_SemanticSchedule.dst r-5)
def output (input : Slice U8) : Slice U8 :=
 ⟨List.ofFn (byte input),by simp only [List.length_ofFn];scalar_tac⟩
theorem source (input before : Slice U8) (inputSize : input.val.length=7015)
 (outputSize : before.val.length=13831) :
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues input before =
 ok (.Ok (),output input) := by
 obtain ⟨final,run,_,size,first,rows⟩ := NGV_SemanticPacket.result input before inputSize outputSize
 have same : final = output input := by
  apply Subtype.ext
  apply List.ext_getElem
  · simpa only [output,List.length_ofFn] using size
  · intro j hj hk
    have bound : j < 13831 := by omega
    let index : Fin 13831 := ⟨j,bound⟩
    have point : final.val[j]?.getD 0#u8 = byte input index := by
     unfold byte
     by_cases early : j < 32
     · rw [dif_pos early]
       exact congrArg (fun x : Option U8 => x.getD 0#u8) (first j early)
     · rw [dif_neg early]
       let row := Row index early
       have live := row.property.1
       have lo : NGD_SemanticSchedule.dst row.val ≤ j := row.property.2.1
       have hi : j < NGD_SemanticSchedule.dst row.val + 5 + NFU_PacketDomains.payloadSize row.val := row.property.2.2
       by_cases header : j < NGD_SemanticSchedule.dst row.val + 5
       · rw [if_pos header]
         have offset : j-NGD_SemanticSchedule.dst row.val < 5 := by omega
         have position : NGD_SemanticSchedule.dst row.val +
           (j-NGD_SemanticSchedule.dst row.val) = j := by omega
         have h := (rows row.val live).1 (j-NGD_SemanticSchedule.dst row.val) offset
         rw [position] at h
         exact congrArg (fun x : Option U8 => x.getD 0#u8) h
       · rw [if_neg header]
         have offset : j-NGD_SemanticSchedule.dst row.val-5 < NFU_PacketDomains.payloadSize row.val := by omega
         have position : NGD_SemanticSchedule.dst row.val + 5 +
          (j-NGD_SemanticSchedule.dst row.val-5) = j := by omega
         have h := (rows row.val live).2 (j-NGD_SemanticSchedule.dst row.val-5) offset
         rw [position] at h
         exact h
    rw [List.getElem?_eq_getElem hj] at point
    simpa only [Option.getD_some,output,List.getElem_ofFn] using point
 simpa only [same] using run
#print axioms source
end LIBC_ExpandSemanticModel
