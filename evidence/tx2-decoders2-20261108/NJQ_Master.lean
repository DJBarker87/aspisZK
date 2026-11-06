import NJQ_Header
import NJQ_Reserved
import NJQ_Identity
import NJQ_MasterBinding
import NJQ_Words
import NJQ_MasterTrace
import NJI_MasterModel
set_option autoImplicit false
noncomputable section
namespace NJQ_Master
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev M := NJI_MasterModel.M
abbrev F := NJI_MasterModel.F
abbrev I := NJQ_Identity.Identity
abbrev P := NJI_PolicyPort.P
abbrev Words := NJQ_Words.Words

def magic : Array U8 4#usize := Array.make 4#usize [65#u8,83#u8,77#u8,56#u8]
def reserved (b : Slice U8) (len : b.val.length=384) : Array U8 14#usize :=
 NHY_NaturalReads.array b 50 14#usize (by change 50+14≤b.val.length;omega)
def tail (b : Slice U8) (len : b.val.length=384) : Array U8 8#usize :=
 NHY_NaturalReads.array b 312 8#usize (by change 312+8≤b.val.length;omega)
def bindingArg (b : Slice U8) (len : b.val.length=384) : Array U8 32#usize :=
 NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega)
def identityArg (b : Slice U8) : Slice U8 := NHY_SliceRead.segment b 64 144
def policyArg (b : Slice U8) : Slice U8 := NHY_SliceRead.segment b 208 104
def sequences (b : Slice U8) (len : b.val.length=384) : Words := NJQ_Words.words b 320 (by omega)

def parseBool (x : U8) : core.result.Result Bool F :=
 match x with | 0#uscalar=>.Ok false | 1#uscalar=>.Ok true | _=>.Err .InvalidBoolean

def record (b : Slice U8) (len : b.val.length=384) (id : I) (policy : P)
 (has : Bool) (lanes : Words) : M :=
 ⟨NHY_ZeroStep.byte b 7,id,policy,NHY_ZeroStep.byte b 48,has,
 NJQ_Words.word b 40 (by omega),lanes⟩

/-- (ah) hand reference, source order and complete child Results. The local-array
loop is represented by its exact word target and NJQ_MasterTrace native induction. -/
def reference (b : Slice U8) : Result (core.result.Result M F) :=
 if len : b.val.length=384 then do
  let head ← NJQ_Header.reference b 384#usize magic
  match head with
  | .Err e=>ok (.Err e)
  | .Ok _=>do
    let region ← NJQ_Read.read b 50#usize 14#usize
    let nonzero ← NJQ_Reserved.master region.to_slice
    if nonzero then ok (.Err .NonZeroReserved) else do
    let last ← NJQ_Read.read b 312#usize 8#usize
    if last.val≠List.replicate 8 0#u8 then ok (.Err .NonZeroReserved) else do
    let observedBinding ← NJQ_Read.read b 8#usize 32#usize
    let expectedBinding ← NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING
    if observedBinding≠expectedBinding then ok (.Err .WrongFormatBinding) else do
    let boolByte ← b.index_usize 49#usize
    match parseBool boolByte with
    | .Err e=>ok (.Err e)
    | .Ok has=>do
      let identityInput ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        b {start:=64#usize,«end»:=208#usize}
      let identity ← NJQ_Identity.reference identityInput
      match identity with
      | .Err _=>ok (.Err .Identity)
      | .Ok id=>do
        let policyInput ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          b {start:=208#usize,«end»:=312#usize}
        let policy ← NJI_PolicyParser.raw policyInput
        match policy with
        | .Err _=>ok (.Err .Policy)
        | .Ok policy=>do
          let lanes := sequences b len
          let bump ← b.index_usize 7#usize
          let mask ← b.index_usize 48#usize
          let next ← NJQ_Read.read b 40#usize 8#usize
          let master : M := ⟨bump,id,policy,mask,has,core.num.U64.from_le_bytes next,lanes⟩
          let checked ← NJI_MasterModel.raw master
          match checked with | .Err e=>ok (.Err e) | .Ok _=>ok (.Ok master)
 else ok (.Err .WrongLength)

def model (b : Slice U8) : Result (core.result.Result M F) :=
 if len : b.val.length=384 then
  match NJQ_Header.model b 384#usize magic with
  | .Err e=>ok (.Err e)
  | .Ok _=>
    if (reserved b len).val≠List.replicate 14 0#u8 then ok (.Err .NonZeroReserved) else
    if (tail b len).val≠List.replicate 8 0#u8 then ok (.Err .NonZeroReserved) else
    if bindingArg b len≠NJQ_MasterBinding.binding then ok (.Err .WrongFormatBinding) else
    match parseBool (NHY_ZeroStep.byte b 49) with
    | .Err e=>ok (.Err e)
    | .Ok has=>do
      let identity ← NJQ_Identity.model (identityArg b)
      match identity with
      | .Err _=>ok (.Err .Identity)
      | .Ok id=>do
        let policy ← NJI_PolicyParser.body (policyArg b)
        match policy with
        | .Err _=>ok (.Err .Policy)
        | .Ok policy=>do
          let master := record b len id policy has (sequences b len)
          let checked ← NJI_MasterModel.model master
          match checked with | .Err e=>ok (.Err e) | .Ok _=>ok (.Ok master)
 else ok (.Err .WrongLength)

theorem child_domains (b : Slice U8) (len : b.val.length=384) :
 (identityArg b).val.length=144 ∧ (policyArg b).val.length=104 := by
 simp only [identityArg,policyArg,NHY_SliceRead.segment,List.length_take,List.length_drop]
 omega

theorem source (b : Slice U8) : reference b=model b := by
 unfold reference model
 split
 · rename_i len
   rw [NJQ_Header.source b 384#usize magic (by change 7≤384;omega)]
   simp only [bind_tc_ok]
   cases hh : NJQ_Header.model b 384#usize magic with
   | Err e=>simp only [hh]
   | Ok u=>
     simp only [hh]
     have r1 : NJQ_Read.read b 50#usize 14#usize=ok (reserved b len) := NJQ_Read.value b _ _ _
     have r2 : NJQ_Read.read b 312#usize 8#usize=ok (tail b len) := NJQ_Read.value b _ _ _
     have rb : NJQ_Read.read b 8#usize 32#usize=ok (bindingArg b len) := NJQ_Read.value b _ _ _
     have b49 := NHY_ZeroStep.read b 49#usize (by change 49<b.val.length;omega)
     have b7 := NHY_ZeroStep.read b 7#usize (by change 7<b.val.length;omega)
     have b48 := NHY_ZeroStep.read b 48#usize (by change 48<b.val.length;omega)
     have seq := NJQ_Read.value b 40#usize 8#usize (by change 40+8≤b.val.length;omega)
     have rid : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
       b {start:=64#usize,«end»:=208#usize}=ok (identityArg b) := by
       have h:=NHY_SliceRead.read b 64#usize 208#usize (by change 64≤208;omega) (by change 208≤b.val.length;omega)
       simpa only [identityArg,show (64#usize).val=64 from rfl,show (208#usize).val=208 from rfl,
         show 208-64=144 from by omega] using h
     have rpol : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
       b {start:=208#usize,«end»:=312#usize}=ok (policyArg b) := by
       have h:=NHY_SliceRead.read b 208#usize 312#usize (by change 208≤312;omega) (by change 312≤b.val.length;omega)
       simpa only [policyArg,show (208#usize).val=208 from rfl,show (312#usize).val=312 from rfl,
         show 312-208=104 from by omega] using h
     have any : NJQ_Reserved.master (reserved b len).to_slice=
       ok (!(decide ((reserved b len).val=List.replicate 14 0#u8))) := by
       simpa only [Array.to_slice,(reserved b len).property,show (14#usize).val=14 from rfl] using NJQ_Reserved.master_value (reserved b len).to_slice
     simp only [r1,r2,rb,any,b49,b7,b48,seq,rid,rpol,bind_tc_ok,NJQ_MasterBinding.source,
       NJQ_Identity.source,NJI_PolicyParser.source,NJI_MasterModel.source]
     by_cases hz : (reserved b len).val=List.replicate 14 0#u8
     · simp only [hz,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,ne_self_iff_false]
       rfl
     · simp only [decide_eq_false hz,Bool.not_false,ite_true,if_pos hz]
 · rename_i wrong
   rfl

set_option pp.proofs false in
#print source
#print axioms child_domains
#print axioms source
end NJQ_Master
