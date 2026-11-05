import NHY_NaturalReads
import NHY_ParsedBodies
import NIS_EntryRecord
set_option autoImplicit false
noncomputable section
namespace NIJ_EntryModel
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Registry := NCX_Reference.VerifierRegistryEntryV2
abbrev FormatError := NCX_Reference.PoolV1VerifierRegistryFormatError
abbrev record := NIJ_EntryRecord.record

def body (b : Slice U8) : Result (core.result.Result Registry FormatError) :=
 if len : b.val.length=320 then
  if b.val.take 4=NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC.val then
   if NHY_ZeroStep.byte b 4=3#u8 then
    if NHY_ZeroStep.byte b 7=1#u8 then
     if (NHY_SliceRead.segment b 314 6).val=List.replicate 6 0#u8 then
      match NIJ_EntryStatus.value (NHY_ZeroStep.byte b 5) with
      | .Err err => ok (.Err err)
      | .Ok status => do
       let reply ← NCX_Reference.validate_verifier_registry_entry_v2 (record b len status)
       ok (NHY_ParsedBodies.validation (record b len status) reply)
     else ok (.Err .NonZeroReserved)
    else ok (.Err .InvalidDeploymentMode)
   else ok (.Err .WrongVersion)
  else ok (.Err .WrongMagic)
 else ok (.Err .WrongLength)

theorem source (b : Slice U8) : NCX_Reference.decode_verifier_registry_entry_v2 b=body b := by
 classical
 unfold body
 split
 · rename_i len
   have size : Slice.len b=320#usize := UScalar.eq_of_val_eq len
   have magic := NHY_NaturalReads.magic b NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC (by omega)
   have version := NHY_ZeroStep.read b 4#usize (by change 4 < b.val.length;omega)
   have mode := NHY_ZeroStep.read b 7#usize (by change 7 < b.val.length;omega)
   have reserved_len := NHY_SliceRead.length b 314 6 (by omega)
   have zero := NHY_NaturalReads.zero (NHY_SliceRead.segment b 314 6) (by omega)
   rw [reserved_len] at zero
   by_cases gm : b.val.take 4=NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC.val
   · simp only [gm,ite_true]
     have hm : NCX_Reference.magic b NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC=ok true := by simpa only [gm,decide_true] using magic
     by_cases gv : NHY_ZeroStep.byte b 4=3#u8
     · simp only [gv,ite_true]
       have hv : Slice.index_usize b 4#usize=ok 3#u8 := by simpa only [show (4#usize).val=4 from rfl,gv] using version
       by_cases gd : NHY_ZeroStep.byte b 7=1#u8
       · simp only [gd,ite_true]
         have hd : Slice.index_usize b 7#usize=ok 1#u8 := by simpa only [show (7#usize).val=7 from rfl,gd] using mode
         by_cases gz : (NHY_SliceRead.segment b 314 6).val=List.replicate 6 0#u8
         · simp only [gz,ite_true]
           have read_status := NHY_ZeroStep.read b 5#usize (by change 5 < b.val.length;omega)
           have parsed_status := NIJ_EntryStatus.source (NHY_ZeroStep.byte b 5)
           cases hs : NIJ_EntryStatus.value (NHY_ZeroStep.byte b 5) with
           | Err err =>
             have eqerr := NIJ_EntryRecord.status_error _ err hs
             subst err
             simp only [hs]
             exact NIJ_EntryStatus.rejected b size hm hv hd
              (by simpa only [gz,decide_true] using zero) _ read_status hs
           | Ok status =>
             simp only [hs]
             apply NHY_ParsedBodies.entry b (record b len status) size hm hv hd
             · simpa only [gz,decide_true] using zero
             · exact read_status
             · simpa only [hs,record,NIJ_EntryRecord.record,show (5#usize).val=5 from rfl] using parsed_status
             · exact NHY_ZeroStep.read b 6#usize (by change 6 < b.val.length;omega)
             · exact NHY_ZeroStep.read b 312#usize (by change 312 < b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 8#usize (by change 8+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 40#usize (by change 40+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 72#usize (by change 72+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 104#usize (by change 104+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 136#usize (by change 136+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 168#usize (by change 168+32 ≤ b.val.length;omega)
             · exact NHY_ZeroStep.read b 313#usize (by change 313 < b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 200#usize (by change 200+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 232#usize (by change 232+32 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.word b 264#usize (by change 264+8 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.word b 272#usize (by change 272+8 ≤ b.val.length;omega)
             · exact NHY_NaturalReads.read32 b 280#usize (by change 280+32 ≤ b.val.length;omega)
         · simp only [gz,ite_false]
           exact NHY_EntryHeader.reserved b size hm hv hd (by simpa only [gz,decide_false] using zero)
       · simp only [gd,ite_false]
         exact NHY_EntryHeader.wrong_mode b size hm hv _ mode gd
     · simp only [gv,ite_false]
       exact NHY_EntryHeader.wrong_version b size hm _ version gv
   · simp only [gm,ite_false]
     exact NHY_EntryHeader.wrong_magic b size (by simpa only [gm,decide_false] using magic)
 · rename_i len
   apply NHY_EntryHeader.wrong_length b
   intro same
   exact len (congrArg UScalar.val same)

#print axioms source
end NIJ_EntryModel
