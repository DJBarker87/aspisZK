import NHY_NaturalReads
import NHY_ParsedBodies
import NHY_RegistryHeader
set_option autoImplicit false
noncomputable section
namespace NHY_RegistryModel
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Registry := NCX_Reference.VerifierRegistryV2
abbrev FormatError := NCX_Reference.PoolV1VerifierRegistryFormatError

def record (b : Slice U8) (len : b.val.length=256) : Registry := {
 flags:=NHY_ZeroStep.byte b 5
 bump:=NHY_ZeroStep.byte b 7
 pool:=NHY_NaturalReads.array b 8 32#usize (by change 8+32 ≤ b.val.length;omega)
 authority:=NHY_NaturalReads.array b 40 32#usize (by change 40+32 ≤ b.val.length;omega)
 policy_binding:=NHY_NaturalReads.array b 72 32#usize (by change 72+32 ≤ b.val.length;omega)
 generation:=core.num.U64.from_le_bytes (NHY_NaturalReads.array b 104 8#usize (by change 104+8 ≤ b.val.length;omega))
 minimum_activation_delay_slots:=core.num.U64.from_le_bytes (NHY_NaturalReads.array b 112 8#usize (by change 112+8 ≤ b.val.length;omega))
 registry_program:=NHY_NaturalReads.array b 120 32#usize (by change 120+32 ≤ b.val.length;omega)
 loader_program:=NHY_NaturalReads.array b 152 32#usize (by change 152+32 ≤ b.val.length;omega)
 programdata_address:=NHY_NaturalReads.array b 184 32#usize (by change 184+32 ≤ b.val.length;omega)
 programdata_bump:=NHY_ZeroStep.byte b 248
 executable_hash:=NHY_NaturalReads.array b 216 32#usize (by change 216+32 ≤ b.val.length;omega)
}

def body (b : Slice U8) : Result (core.result.Result Registry FormatError) :=
 if len : b.val.length=256 then
  if b.val.take 4=NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC.val then
   if NHY_ZeroStep.byte b 4=3#u8 then
    if NHY_ZeroStep.byte b 6=1#u8 then
     if (NHY_SliceRead.segment b 249 7).val=List.replicate 7 0#u8 then do
      let reply ← NCX_Reference.validate_verifier_registry_v2 (record b len)
      ok (NHY_ParsedBodies.validation (record b len) reply)
     else ok (.Err .NonZeroReserved)
    else ok (.Err .InvalidDeploymentMode)
   else ok (.Err .WrongVersion)
  else ok (.Err .WrongMagic)
 else ok (.Err .WrongLength)

theorem source (b : Slice U8) : NCX_Reference.decode_verifier_registry_v2 b=body b := by
 classical
 unfold body
 split
 · rename_i len
   have size : Slice.len b=256#usize := UScalar.eq_of_val_eq len
   have magic := NHY_NaturalReads.magic b NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC (by omega)
   have version := NHY_ZeroStep.read b 4#usize (by change 4 < b.val.length;omega)
   have mode := NHY_ZeroStep.read b 6#usize (by change 6 < b.val.length;omega)
   have reserved_len := NHY_SliceRead.length b 249 7 (by omega)
   have zero := NHY_NaturalReads.zero (NHY_SliceRead.segment b 249 7) (by omega)
   rw [reserved_len] at zero
   by_cases gm : b.val.take 4=NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC.val
   · simp only [gm,ite_true]
     have hm : NCX_Reference.magic b NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok true := by simpa only [gm,decide_true] using magic
     by_cases gv : NHY_ZeroStep.byte b 4=3#u8
     · simp only [gv,ite_true]
       have hv : Slice.index_usize b 4#usize=ok 3#u8 := by simpa only [show (4#usize).val=4 from rfl,gv] using version
       by_cases gd : NHY_ZeroStep.byte b 6=1#u8
       · simp only [gd,ite_true]
         have hd : Slice.index_usize b 6#usize=ok 1#u8 := by simpa only [show (6#usize).val=6 from rfl,gd] using mode
         by_cases gz : (NHY_SliceRead.segment b 249 7).val=List.replicate 7 0#u8
         · simp only [gz,ite_true]
           apply NHY_ParsedBodies.registry b (record b len) size hm hv hd
           · simpa only [gz,decide_true] using zero
           · exact NHY_ZeroStep.read b 5#usize (by change 5 < b.val.length;omega)
           · exact NHY_ZeroStep.read b 7#usize (by change 7 < b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 8#usize (by change 8+32 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 40#usize (by change 40+32 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 72#usize (by change 72+32 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.word b 104#usize (by change 104+8 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.word b 112#usize (by change 112+8 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 120#usize (by change 120+32 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 152#usize (by change 152+32 ≤ b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 184#usize (by change 184+32 ≤ b.val.length;omega)
           · exact NHY_ZeroStep.read b 248#usize (by change 248 < b.val.length;omega)
           · exact NHY_NaturalReads.read32 b 216#usize (by change 216+32 ≤ b.val.length;omega)
         · simp only [gz,ite_false]
           exact NHY_RegistryHeader.reserved b size hm hv hd (by simpa only [gz,decide_false] using zero)
       · simp only [gd,ite_false]
         exact NHY_RegistryHeader.wrong_mode b size hm hv _ mode gd
     · simp only [gv,ite_false]
       exact NHY_RegistryHeader.wrong_version b size hm _ version gv
   · simp only [gm,ite_false]
     exact NHY_RegistryHeader.wrong_magic b size (by simpa only [gm,decide_false] using magic)
 · rename_i len
   apply NHY_RegistryHeader.wrong_length b
   intro same
   exact len (congrArg UScalar.val same)

#print axioms source
end NHY_RegistryModel
