import NJQ_Read
set_option autoImplicit false
noncomputable section
namespace NJQ_Identity
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Identity := NJI_Extracted.aspis_statement.pool_v1.format.PoolIdentityV1
abbrev Error := NJI_Extracted.aspis_statement.pool_v1.format.PoolV1FormatError

def magic : Array U8 4#usize := Array.make 4#usize [65#u8,83#u8,80#u8,73#u8]

def record (b : Slice U8) (len : b.val.length=144) : Identity :=
 ⟨NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega),
 NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega),
 NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega),
 core.num.U32.from_le_bytes (NHY_NaturalReads.array b 104 4#usize (by change 104+4≤b.val.length;omega)),
 NHY_NaturalReads.array b 112 32#usize (by change 112+32≤b.val.length;omega)⟩

/-- (ah) hand transcription of NJQ_identity::decode_ref, not Aeneas output.
Ranges/casts/unwrap use P7 via NJQ_Read; ordered guards retain all errors. -/
def reference (b : Slice U8) : Result (core.result.Result Identity Error) :=
 if Slice.len b != 144#usize then ok (.Err .WrongLength) else do
 let header ← NCX_Reference.magic b magic
 if !header then ok (.Err .WrongMagic) else do
 let version ← b.index_usize 4#usize
 if version != 1#u8 then ok (.Err .WrongVersion) else do
 let reserved1 ← NJQ_Read.read b 5#usize 3#usize
 if reserved1.val ≠ List.replicate 3 0#u8 then ok (.Err .NonZeroReserved) else do
 let reserved2 ← NJQ_Read.read b 108#usize 4#usize
 if reserved2.val ≠ List.replicate 4 0#u8 then ok (.Err .NonZeroReserved) else do
 let word ← NJQ_Read.read b 104#usize 4#usize
 let raw := core.num.U32.from_le_bytes word
 if raw >= 2147483647#u32 then ok (.Err .NonCanonicalAssetId) else do
 let pool ← NJQ_Read.read b 8#usize 32#usize
 let mint ← NJQ_Read.read b 40#usize 32#usize
 let token ← NJQ_Read.read b 72#usize 32#usize
 let domain ← NJQ_Read.read b 112#usize 32#usize
 ok (.Ok ⟨pool,mint,token,raw,domain⟩)

def model (b : Slice U8) : Result (core.result.Result Identity Error) :=
 if len : b.val.length=144 then
  if b.val.take 4=magic.val then
   if NHY_ZeroStep.byte b 4=1#u8 then
    if (b.val.drop 5).take 3=List.replicate 3 0#u8 ∧
       (b.val.drop 108).take 4=List.replicate 4 0#u8 then
     if (record b len).asset_id < 2147483647#u32 then ok (.Ok (record b len))
     else ok (.Err .NonCanonicalAssetId)
    else ok (.Err .NonZeroReserved)
   else ok (.Err .WrongVersion)
  else ok (.Err .WrongMagic)
 else ok (.Err .WrongLength)

theorem source (b : Slice U8) : reference b=model b := by
 unfold model
 split
 · rename_i len
   have size : Slice.len b=144#usize := UScalar.eq_of_val_eq len
   have header := NHY_NaturalReads.magic b magic (by omega)
   have version := NHY_ZeroStep.read b 4#usize (by change 4<b.val.length;omega)
   have r1 := NJQ_Read.value b 5#usize 3#usize (by change 5+3≤b.val.length;omega)
   have r2 := NJQ_Read.value b 108#usize 4#usize (by change 108+4≤b.val.length;omega)
   have word := NJQ_Read.value b 104#usize 4#usize (by change 104+4≤b.val.length;omega)
   have pool := NJQ_Read.value b 8#usize 32#usize (by change 8+32≤b.val.length;omega)
   have mint := NJQ_Read.value b 40#usize 32#usize (by change 40+32≤b.val.length;omega)
   have token := NJQ_Read.value b 72#usize 32#usize (by change 72+32≤b.val.length;omega)
   have domain := NJQ_Read.value b 112#usize 32#usize (by change 112+32≤b.val.length;omega)
   simp only [reference,size,show (144#usize != 144#usize)=false from rfl,
    Bool.false_eq_true,ite_false,header,version,r1,r2,word,pool,mint,token,domain,bind_tc_ok]
   simp only [show (4#usize).val=4 from rfl, show (5#usize).val=5 from rfl, show (108#usize).val=108 from rfl]
   by_cases hm : b.val.take 4=magic.val
   · simp only [hm,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
     by_cases hv : NHY_ZeroStep.byte b 4=1#u8
     · simp only [hv,show (1#u8 != 1#u8)=false from rfl,Bool.false_eq_true,ite_false,ite_true]
       by_cases h1 : (b.val.drop 5).take 3=List.replicate 3 0#u8
       · by_cases h2 : (b.val.drop 108).take 4=List.replicate 4 0#u8
         · simp only [NHY_NaturalReads.array, show (3#usize).val=3 from rfl,
            show (4#usize).val=4 from rfl, h1,h2,not_true_eq_false,ite_false,true_and,ite_true]
           change (if 2147483647≤(record b len).asset_id.val then _ else _) =
             (if (record b len).asset_id.val<2147483647 then _ else _)
           by_cases ha : (record b len).asset_id.val<2147483647
           · rw [if_neg (Nat.not_le.mpr ha),if_pos ha];rfl
           · rw [if_pos (Nat.le_of_not_gt ha),if_neg ha]
         · simp only [NHY_NaturalReads.array,show (3#usize).val=3 from rfl,show (4#usize).val=4 from rfl,h1,h2,
             ne_self_iff_false,not_true_eq_false,not_false_eq_true,not_not,ite_false,ite_true,true_and]
           rw [if_pos h2]
       · simp only [NHY_NaturalReads.array,show (3#usize).val=3 from rfl,h1,ne_self_iff_false,not_true_eq_false,not_false_eq_true,not_not,ite_true,false_and,ite_false]
         rw [if_pos h1]
     · simp [hv]
   · simp [hm]
 · rename_i len
   have size : Slice.len b≠144#usize := by intro eq;exact len (congrArg UScalar.val eq)
   simp [reference,size]

#print source
#print axioms source
end NJQ_Identity
