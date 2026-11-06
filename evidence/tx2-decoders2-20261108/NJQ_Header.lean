import NJQ_Read
set_option autoImplicit false
noncomputable section
namespace NJQ_Header
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev F := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1

def reference (b : Slice U8) (width : Usize) (magic : Array U8 4#usize) :
 Result (core.result.Result Unit F) :=
 if Slice.len b != width then ok (.Err .WrongLength) else do
 let header ← NCX_Reference.magic b magic
 if !header then ok (.Err .WrongMagic) else do
 let version ← b.index_usize 4#usize
 if version != 2#u8 then ok (.Err .WrongVersion) else do
 let lanes ← b.index_usize 5#usize
 if lanes != 8#u8 then ok (.Err .WrongLaneCount) else do
 let encoding ← b.index_usize 6#usize
 if encoding != 1#u8 then ok (.Err .WrongDigestEncoding) else ok (.Ok ())

def model (b : Slice U8) (width : Usize) (magic : Array U8 4#usize) :
 core.result.Result Unit F :=
 if b.val.length≠width.val then .Err .WrongLength
 else if b.val.take 4≠magic.val then .Err .WrongMagic
 else if NHY_ZeroStep.byte b 4≠2#u8 then .Err .WrongVersion
 else if NHY_ZeroStep.byte b 5≠8#u8 then .Err .WrongLaneCount
 else if NHY_ZeroStep.byte b 6≠1#u8 then .Err .WrongDigestEncoding
 else .Ok ()

theorem source (b : Slice U8) (width : Usize) (magic : Array U8 4#usize)
 (large : 7≤width.val) : reference b width magic=ok (model b width magic) := by
 by_cases len : b.val.length=width.val
 · have size : Slice.len b=width := UScalar.eq_of_val_eq len
   have head := NHY_NaturalReads.magic b magic (by omega)
   have v4 := NHY_ZeroStep.read b 4#usize (by change 4<b.val.length;omega)
   have v5 := NHY_ZeroStep.read b 5#usize (by change 5<b.val.length;omega)
   have v6 := NHY_ZeroStep.read b 6#usize (by change 6<b.val.length;omega)
   simp only [reference,size,show (width != width)=false from by simp,Bool.false_eq_true,ite_false,
    head,v4,v5,v6,bind_tc_ok,model,len,not_true_eq_false]
   simp only [show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,show (6#usize).val=6 from rfl]
   by_cases hm : b.val.take 4=magic.val <;>
    by_cases hv : NHY_ZeroStep.byte b 4=2#u8 <;>
    by_cases hl : NHY_ZeroStep.byte b 5=8#u8 <;>
    by_cases hd : NHY_ZeroStep.byte b 6=1#u8 <;> simp_all
 · have size : Slice.len b≠width := by intro same;exact len (congrArg UScalar.val same)
   simp [reference,model,size,len]

#print axioms source
end NJQ_Header
