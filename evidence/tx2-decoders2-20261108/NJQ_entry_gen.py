"""Generate the explicit hand reference and natural parser model; no extraction."""
from pathlib import Path
E=Path(__file__).resolve().parent
fields=[('pool',8,32),('verifier_program',40,32),('profile_binding',72,32),('release_binding',104,32),('activation_slot',136,8),('retirement_slot',144,8),('policy_binding',152,32)]
def arr(o,n):return f'NHY_NaturalReads.array b {o} {n}#usize (by change {o}+{n}≤b.val.length;omega)'
status='NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from'
s='''import NJQ_Read
import NJI_V1Join
set_option autoImplicit false
noncomputable section
namespace NJQ_Entry
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable
abbrev Status := NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1
def magic : Array U8 4#usize := Array.make 4#usize [65#u8,83#u8,82#u8,69#u8]
'''
s+='def record (b : Slice U8) (len : b.val.length=192) (status : Status) : E :=\n ⟨status,NHY_ZeroStep.byte b 6,NHY_ZeroStep.byte b 7,\n '
s+=',\n '.join(('core.num.U64.from_le_bytes ('+arr(o,n)+')' if n==8 else arr(o,n)) for _,o,n in fields)+'⟩\n'
s+='''def finish (r : E) : Result (core.result.Result E F) := do
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
 let converted ← '''+status+''' rawStatus
 match converted with
 | .Err e => ok (.Err e)
 | .Ok status => do
   let statementVersion ← b.index_usize 6#usize
   let bump ← b.index_usize 7#usize
'''
for name,o,n in fields:s+=f'   let {name} ← NJQ_Read.read b {o}#usize {n}#usize\n'
s+='   finish ⟨status,statementVersion,bump,'+','.join(('core.num.U64.from_le_bytes '+name if n==8 else name) for name,_,n in fields)+'⟩\n'
s+='''
def model (b : Slice U8) : Result (core.result.Result E F) :=
 if len : b.val.length=192 then
  if b.val.take 4=magic.val then
   if NHY_ZeroStep.byte b 4=2#u8 then
    if (b.val.drop 184).take 8=List.replicate 8 0#u8 then do
     let converted ← '''+status+''' (NHY_ZeroStep.byte b 5)
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
'''
for i in [4,5,6,7]:s+=f'   have v{i} := NHY_ZeroStep.read b {i}#usize (by change {i}<b.val.length;omega)\n'
for name,o,n in [('tail',184,8)]+fields:s+=f'   have {name} := NJQ_Read.value b {o}#usize {n}#usize (by change {o}+{n}≤b.val.length;omega)\n'
s+='''   simp only [reference,size,show (192#usize != 192#usize)=false from rfl,Bool.false_eq_true,ite_false,
    header,v4,v5,v6,v7,tail,'''+','.join(name for name,_,_ in fields)+''',bind_tc_ok]
   simp only [show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,
     show (6#usize).val=6 from rfl,show (7#usize).val=7 from rfl]
   by_cases hm : b.val.take 4=magic.val
   · simp only [hm,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
     by_cases hv : NHY_ZeroStep.byte b 4=2#u8
     · simp only [hv,show (2#u8 != 2#u8)=false from rfl,Bool.false_eq_true,ite_false,ite_true]
       by_cases hz : (b.val.drop 184).take 8=List.replicate 8 0#u8
       · simp only [NHY_NaturalReads.array,show (8#usize).val=8 from rfl,show (184#usize).val=184 from rfl,hz,ne_self_iff_false,not_true_eq_false,ite_false,ite_true]
         simp only [record,finish,NJI_V1Models.entry_source]
         rfl
       · simp only [NHY_NaturalReads.array,show (8#usize).val=8 from rfl,show (184#usize).val=184 from rfl,hz,ite_false]
         rw [if_pos hz]
     · simp [hv]
   · simp [hm]
 · rename_i len
   have size : Slice.len b≠192#usize := by intro eq;exact len (congrArg UScalar.val eq)
   simp [reference,size]

#print source
#print axioms source
end NJQ_Entry
'''
(E/'NJQ_Entry.lean').write_text(s)
print('Entry full Result hand parser generated; no extraction.')
