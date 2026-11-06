import NJQ_Read
import NJI_V1Join
set_option autoImplicit false
noncomputable section
namespace NJQ_Entry
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable
abbrev Status := NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1
def magic : Array U8 4#usize := Array.make 4#usize [65#u8,83#u8,82#u8,69#u8]
def record (b : Slice U8) (len : b.val.length=192) (status : Status) : E :=
 ⟨status,NHY_ZeroStep.byte b 6,NHY_ZeroStep.byte b 7,
 NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega),
 NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega),
 NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega),
 NHY_NaturalReads.array b 104 32#usize (by change 104+32≤b.val.length;omega),
 core.num.U64.from_le_bytes (NHY_NaturalReads.array b 136 8#usize (by change 136+8≤b.val.length;omega)),
 core.num.U64.from_le_bytes (NHY_NaturalReads.array b 144 8#usize (by change 144+8≤b.val.length;omega)),
 NHY_NaturalReads.array b 152 32#usize (by change 152+32≤b.val.length;omega)⟩
def finish (r : E) : Result (core.result.Result E F) := do
 let checked ← NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1 r
 match checked with | .Ok _ => ok (.Ok r) | .Err e => ok (.Err e)

def reference (b : Slice U8) : Result (core.result.Result E F) :=
 if Slice.len b != 192#usize then ok (.Err .WrongLength) else do
 let header ← NCX_Reference.magic b magic
 if !header then ok (.Err .WrongMagic) else do
 let version ← b.index_usize 4#usize
 if version != 2#u8 then ok (.Err .WrongVersion) else do
 let tail ← NJQ_Read.read b 184#usize 8#usize
 if tail.val ≠ List.replicate 8 0#u8 then ok (.Err .NonZeroReserved) else do
 let rawStatus ← b.index_usize 5#usize
 let converted ← NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from rawStatus
 match converted with
 | .Err e => ok (.Err e)
 | .Ok status => do
   let statementVersion ← b.index_usize 6#usize
   let bump ← b.index_usize 7#usize
   let pool ← NJQ_Read.read b 8#usize 32#usize
   let verifier_program ← NJQ_Read.read b 40#usize 32#usize
   let profile_binding ← NJQ_Read.read b 72#usize 32#usize
   let release_binding ← NJQ_Read.read b 104#usize 32#usize
   let activation_slot ← NJQ_Read.read b 136#usize 8#usize
   let retirement_slot ← NJQ_Read.read b 144#usize 8#usize
   let policy_binding ← NJQ_Read.read b 152#usize 32#usize
   finish ⟨status,statementVersion,bump,pool,verifier_program,profile_binding,release_binding,core.num.U64.from_le_bytes activation_slot,core.num.U64.from_le_bytes retirement_slot,policy_binding⟩

def model (b : Slice U8) : Result (core.result.Result E F) :=
 if len : b.val.length=192 then
  if b.val.take 4=magic.val then
   if NHY_ZeroStep.byte b 4=2#u8 then
    if (b.val.drop 184).take 8=List.replicate 8 0#u8 then do
     let converted ← NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from (NHY_ZeroStep.byte b 5)
     match converted with
     | .Err e => ok (.Err e)
     | .Ok status => do
       let checked ← NJI_V1Models.entry (record b len status)
       match checked with | .Ok _ => ok (.Ok (record b len status)) | .Err e => ok (.Err e)
    else ok (.Err .NonZeroReserved)
   else ok (.Err .WrongVersion)
  else ok (.Err .WrongMagic)
 else ok (.Err .WrongLength)

theorem source (b : Slice U8) : reference b=model b := by
 unfold model
 split
 · rename_i len
   have size : Slice.len b=192#usize := UScalar.eq_of_val_eq len
   have header := NHY_NaturalReads.magic b magic (by omega)
   have v4 := NHY_ZeroStep.read b 4#usize (by change 4<b.val.length;omega)
   have v5 := NHY_ZeroStep.read b 5#usize (by change 5<b.val.length;omega)
   have v6 := NHY_ZeroStep.read b 6#usize (by change 6<b.val.length;omega)
   have v7 := NHY_ZeroStep.read b 7#usize (by change 7<b.val.length;omega)
   have tail := NJQ_Read.value b 184#usize 8#usize (by change 184+8≤b.val.length;omega)
   have pool := NJQ_Read.value b 8#usize 32#usize (by change 8+32≤b.val.length;omega)
   have verifier_program := NJQ_Read.value b 40#usize 32#usize (by change 40+32≤b.val.length;omega)
   have profile_binding := NJQ_Read.value b 72#usize 32#usize (by change 72+32≤b.val.length;omega)
   have release_binding := NJQ_Read.value b 104#usize 32#usize (by change 104+32≤b.val.length;omega)
   have activation_slot := NJQ_Read.value b 136#usize 8#usize (by change 136+8≤b.val.length;omega)
   have retirement_slot := NJQ_Read.value b 144#usize 8#usize (by change 144+8≤b.val.length;omega)
   have policy_binding := NJQ_Read.value b 152#usize 32#usize (by change 152+32≤b.val.length;omega)
   simp only [reference,size,show (192#usize != 192#usize)=false from rfl,Bool.false_eq_true,ite_false,
    header,v4,v5,v6,v7,tail,pool,verifier_program,profile_binding,release_binding,activation_slot,retirement_slot,policy_binding,bind_tc_ok]
   simp only [show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,
     show (6#usize).val=6 from rfl,show (7#usize).val=7 from rfl]
   by_cases hm : b.val.take 4=magic.val
   · simp only [hm,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
     by_cases hv : NHY_ZeroStep.byte b 4=2#u8
     · simp only [hv,show (2#u8 != 2#u8)=false from rfl,Bool.false_eq_true,ite_false,ite_true]
       by_cases hz : (b.val.drop 184).take 8=List.replicate 8 0#u8
       · simp only [NHY_NaturalReads.array,show (8#usize).val=8 from rfl,show (184#usize).val=184 from rfl,hz,not_true_eq_false,ite_false,ite_true]
         simp only [record,finish,NJI_V1Models.entry_source]
       · simp [hz,NHY_NaturalReads.array]
     · simp [hv]
   · simp [hm]
 · rename_i len
   have size : Slice.len b≠192#usize := by intro eq;exact len (congrArg UScalar.val eq)
   simp [reference,size]

#print source
#print axioms source
end NJQ_Entry
