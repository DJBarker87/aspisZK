import NJQ_Header
import NJQ_Reserved
import NJQ_DigestPort
import NJQ_ArrayAll
set_option autoImplicit false
noncomputable section
namespace NJQ_Checkpoint
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev C := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
abbrev F := NJQ_Header.F
abbrev Digest := NJQ_DigestPort.Digest
abbrev Words := NJQ_Words.Words

def magic : Array U8 4#usize := Array.make 4#usize [65#u8,83#u8,67#u8,56#u8]
def trailing (b : Slice U8) (len : b.val.length=192) : Array U8 16#usize :=
 NHY_NaturalReads.array b 176 16#usize (by change 176+16≤b.val.length;omega)
def masterBytes (b : Slice U8) (len : b.val.length=192) : Array U8 32#usize :=
 NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega)
def domainBytes (b : Slice U8) (len : b.val.length=192) : Array U8 32#usize :=
 NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega)
def digestArg (b : Slice U8) (len : b.val.length=192) : Array U8 32#usize :=
 NHY_NaturalReads.array b 80 32#usize (by change 80+32≤b.val.length;omega)
def sequences (b : Slice U8) (len : b.val.length=192) : Words :=
 NJQ_Words.words b 112 (by omega)
def record (b : Slice U8) (len : b.val.length=192) (root : Digest) (lanes : Words) : C :=
 ⟨NHY_ZeroStep.byte b 7,masterBytes b len,domainBytes b len,
  NJQ_Words.word b 72 (by omega),root,lanes⟩

/-- Hand reference under (ah). The loop term is source-ordered scan, with
native one-step/finite-induction association NJQ_ArrayAll.native_result. -/
def reference (b : Slice U8) : Result (core.result.Result C F) :=
 if len : b.val.length=192 then do
  let head ← NJQ_Header.reference b 192#usize magic
  match head with
  | .Err e=>ok (.Err e)
  | .Ok _=>do
    let tail ← NJQ_Read.read b 176#usize 16#usize
    let nonzero ← NJQ_Reserved.checkpoint tail.to_slice
    if nonzero then ok (.Err .NonZeroReserved) else do
    let master ← NJQ_Read.read b 8#usize 32#usize
    let domain ← NJQ_Read.read b 40#usize 32#usize
    if master=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding) else
    if domain=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding) else do
    let arg ← NJQ_Read.read b 80#usize 32#usize
    let digest ← NJQ_DigestPort.canonical arg
    match digest with
    | .Err _=>ok (.Err .NonCanonicalDigest)
    | .Ok root=>
      match NJQ_ArrayAll.loop (sequences b len) with
      | .Err e=>ok (.Err e)
      | .Ok lanes=>do
        let bump ← b.index_usize 7#usize
        let seq ← NJQ_Read.read b 72#usize 8#usize
        ok (.Ok ⟨bump,master,domain,core.num.U64.from_le_bytes seq,root,lanes⟩)
 else ok (.Err .WrongLength)

def model (b : Slice U8) : Result (core.result.Result C F) :=
 if len : b.val.length=192 then
  match NJQ_Header.model b 192#usize magic with
  | .Err e=>ok (.Err e)
  | .Ok _=>
    if (trailing b len).val≠List.replicate 16 0#u8 then ok (.Err .NonZeroReserved) else
    if masterBytes b len=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding) else
    if domainBytes b len=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding) else
    match NJQ_DigestPort.decoded (digestArg b len) with
    | .Err _=>ok (.Err .NonCanonicalDigest)
    | .Ok root=>
      match NJQ_ArrayAll.loop (sequences b len) with
      | .Err e=>ok (.Err e)
      | .Ok lanes=>ok (.Ok (record b len root lanes))
 else ok (.Err .WrongLength)

theorem source (b : Slice U8) : reference b=model b := by
 unfold reference model
 split
 · rename_i len
   rw [NJQ_Header.source b 192#usize magic (by change 7≤192;omega)]
   simp only [bind_tc_ok]
   cases hh : NJQ_Header.model b 192#usize magic with
   | Err e=>simp only [hh]
   | Ok u=>
     simp only [hh]
     have rt : NJQ_Read.read b 176#usize 16#usize=ok (trailing b len) := NJQ_Read.value b _ _ _
     have rm : NJQ_Read.read b 8#usize 32#usize=ok (masterBytes b len) := NJQ_Read.value b _ _ _
     have rd : NJQ_Read.read b 40#usize 32#usize=ok (domainBytes b len) := NJQ_Read.value b _ _ _
     have rg : NJQ_Read.read b 80#usize 32#usize=ok (digestArg b len) := NJQ_Read.value b _ _ _
     have rs := NJQ_Read.value b 72#usize 8#usize (by change 72+8≤b.val.length;omega)
     have rb := NHY_ZeroStep.read b 7#usize (by change 7<b.val.length;omega)
     have any : NJQ_Reserved.checkpoint (trailing b len).to_slice=
       ok (!(decide ((trailing b len).val=List.replicate 16 0#u8))) := by
       simpa only [Array.to_slice,(trailing b len).property,show (16#usize).val=16 from rfl] using NJQ_Reserved.checkpoint_value (trailing b len).to_slice
     simp only [rt,rm,rd,rg,rs,rb,bind_tc_ok,any,NJQ_DigestPort.source]
     by_cases hz : (trailing b len).val=List.replicate 16 0#u8
     · simp only [hz,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,ne_self_iff_false]
       by_cases hm : masterBytes b len=Array.repeat 32#usize 0#u8 <;>
        by_cases hd : domainBytes b len=Array.repeat 32#usize 0#u8 <;> simp only [hm,hd,ite_true,ite_false]
       all_goals
        cases hg : NJQ_DigestPort.decoded (digestArg b len) with
        | Err e=>simp only [hg,bind_tc_ok]
        | Ok root=>
          simp only [hg,bind_tc_ok]
          cases hl : NJQ_ArrayAll.loop (sequences b len) with
          | Err e=>simp only [hl]
          | Ok lanes=>simp only [hl];rfl
     · simp only [decide_eq_false hz,Bool.not_false,ite_true,if_pos hz]
 · rename_i wrong
   rfl

set_option pp.proofs false in
#print source
#print axioms source
end NJQ_Checkpoint
