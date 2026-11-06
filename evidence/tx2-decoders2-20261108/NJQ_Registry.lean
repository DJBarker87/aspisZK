import NJQ_Read
import NJI_V1Join
set_option autoImplicit false
noncomputable section
namespace NJQ_Registry
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable

def magic : Array U8 4#usize := Array.make 4#usize [65#u8,83#u8,82#u8,71#u8]
def record (b : Slice U8) (len : b.val.length=128) : R :=
 ⟨NHY_ZeroStep.byte b 5,NHY_ZeroStep.byte b 6,
 NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega),
 NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega),
 NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega),
 core.num.U64.from_le_bytes (NHY_NaturalReads.array b 104 8#usize (by change 104+8≤b.val.length;omega)),
 core.num.U64.from_le_bytes (NHY_NaturalReads.array b 112 8#usize (by change 112+8≤b.val.length;omega))⟩

def finish (r : R) : Result (core.result.Result R F) := do
 let checked ← NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1 r
 match checked with | .Ok _ => ok (.Ok r) | .Err e => ok (.Err e)

def reference (b : Slice U8) : Result (core.result.Result R F) :=
 if Slice.len b != 128#usize then ok (.Err .WrongLength) else do
 let header ← NCX_Reference.magic b magic
 if !header then ok (.Err .WrongMagic) else do
 let version ← b.index_usize 4#usize
 if version != 2#u8 then ok (.Err .WrongVersion) else do
 let reserved ← b.index_usize 7#usize
 if reserved != 0#u8 then ok (.Err .NonZeroReserved) else do
 let tail ← NJQ_Read.read b 120#usize 8#usize
 if tail.val ≠ List.replicate 8 0#u8 then ok (.Err .NonZeroReserved) else do
 let flags ← b.index_usize 5#usize
 let bump ← b.index_usize 6#usize
 let pool ← NJQ_Read.read b 8#usize 32#usize
 let authority ← NJQ_Read.read b 40#usize 32#usize
 let binding ← NJQ_Read.read b 72#usize 32#usize
 let generation ← NJQ_Read.read b 104#usize 8#usize
 let delay ← NJQ_Read.read b 112#usize 8#usize
 finish ⟨flags,bump,pool,authority,binding,core.num.U64.from_le_bytes generation,core.num.U64.from_le_bytes delay⟩

def model (b : Slice U8) : Result (core.result.Result R F) :=
 if len : b.val.length=128 then
  if b.val.take 4=magic.val then
   if NHY_ZeroStep.byte b 4=2#u8 then
    if NHY_ZeroStep.byte b 7=0#u8 ∧ (b.val.drop 120).take 8=List.replicate 8 0#u8 then do
     let checked ← NJI_V1Models.registry (record b len)
     match checked with | .Ok _ => ok (.Ok (record b len)) | .Err e => ok (.Err e)
    else ok (.Err .NonZeroReserved)
   else ok (.Err .WrongVersion)
  else ok (.Err .WrongMagic)
 else ok (.Err .WrongLength)

theorem source (b : Slice U8) : reference b=model b := by
 unfold model
 split
 · rename_i len
   have size : Slice.len b=128#usize := UScalar.eq_of_val_eq len
   have header := NHY_NaturalReads.magic b magic (by omega)
   have v4 := NHY_ZeroStep.read b 4#usize (by change 4<b.val.length;omega)
   have v5 := NHY_ZeroStep.read b 5#usize (by change 5<b.val.length;omega)
   have v6 := NHY_ZeroStep.read b 6#usize (by change 6<b.val.length;omega)
   have v7 := NHY_ZeroStep.read b 7#usize (by change 7<b.val.length;omega)
   have tail := NJQ_Read.value b 120#usize 8#usize (by change 120+8≤b.val.length;omega)
   have pool := NJQ_Read.value b 8#usize 32#usize (by change 8+32≤b.val.length;omega)
   have authority := NJQ_Read.value b 40#usize 32#usize (by change 40+32≤b.val.length;omega)
   have binding := NJQ_Read.value b 72#usize 32#usize (by change 72+32≤b.val.length;omega)
   have generation := NJQ_Read.value b 104#usize 8#usize (by change 104+8≤b.val.length;omega)
   have delay := NJQ_Read.value b 112#usize 8#usize (by change 112+8≤b.val.length;omega)
   simp only [reference,size,show (128#usize != 128#usize)=false from rfl,Bool.false_eq_true,ite_false,
    header,v4,v5,v6,v7,tail,pool,authority,binding,generation,delay,bind_tc_ok]
   simp only [show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,show (6#usize).val=6 from rfl,show (7#usize).val=7 from rfl]
   by_cases hm : b.val.take 4=magic.val
   · simp only [hm,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
     by_cases hv : NHY_ZeroStep.byte b 4=2#u8
     · simp only [hv,show (2#u8 != 2#u8)=false from rfl,Bool.false_eq_true,ite_false,ite_true]
       by_cases h7 : NHY_ZeroStep.byte b 7=0#u8
       · simp only [h7,show (0#u8 != 0#u8)=false from rfl,Bool.false_eq_true,ite_false,true_and]
         by_cases hz : (b.val.drop 120).take 8=List.replicate 8 0#u8
         · simp only [NHY_NaturalReads.array,show (8#usize).val=8 from rfl,show (120#usize).val=120 from rfl,
             hz,ne_self_iff_false,ite_false,ite_true]
           change finish (record b len) = _
           simp only [finish,NJI_V1Models.registry_source]
           rfl
         · simp only [NHY_NaturalReads.array,show (8#usize).val=8 from rfl,show (120#usize).val=120 from rfl,
             hz,ite_false]
           rw [if_pos hz]
       · simp [h7]
     · simp [hv]
   · simp [hm]
 · rename_i len
   have size : Slice.len b≠128#usize := by intro eq;exact len (congrArg UScalar.val eq)
   simp [reference,size]

#print source
#print axioms source
end NJQ_Registry
