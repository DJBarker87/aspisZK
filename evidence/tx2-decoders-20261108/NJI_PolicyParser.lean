import NJI_PolicyPort
import NJI_StdNe
import NHY_NaturalReads
set_option autoImplicit false
noncomputable section
namespace NJI_PolicyParser
open Aeneas Aeneas.Std Result
open NJI_PolicyPort
attribute [local instance] Classical.propDecidable
abbrev magic := NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_VERIFIER_POLICY_MAGIC

def record (b : Slice U8) (len : b.val.length=104) : P :=
 ⟨NHY_ZeroStep.byte b 5,
  NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega),
  NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega),
  NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega)⟩

def validation (p : P) (r : core.result.Result Unit F) : core.result.Result P F :=
 match r with | .Ok _ => .Ok p | .Err e => .Err e

def body (b : Slice U8) : Result (core.result.Result P F) :=
 if len : b.val.length=104 then
  if b.val.take 4=magic.val then
   if NHY_ZeroStep.byte b 4=1#u8 then
    if (b.val.drop 6).take 2=List.replicate 2 0#u8 then do
      let reply ← validator (record b len)
      ok (validation (record b len) reply)
    else ok (.Err .NonZeroReserved)
   else ok (.Err .WrongVersion)
  else ok (.Err .WrongMagic)
 else ok (.Err .WrongLength)

def raw (b : Slice U8) :=
 NJI_Extracted.aspis_statement.pool_v1.format.decode_verifier_policy_v1 NJI_StdNe.ne validator b

/-- Full parser domain, all rejection arms; CLOSED op15 is supplied on the SAME record. -/
theorem source (b : Slice U8) : raw b=body b := by
 have count : NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_VERIFIER_POLICY_BYTES=104#usize := by
  unfold NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_VERIFIER_POLICY_BYTES
  rfl
 have version : NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_VERIFIER_POLICY_VERSION=1#u8 := by
  unfold NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_VERIFIER_POLICY_VERSION
  rfl
 unfold body
 split
 · rename_i len
   have size : Slice.len b=104#usize := UScalar.eq_of_val_eq len
   have pre := NHY_NaturalReads.read_prefix b 4#usize (by change 4≤b.val.length;omega)
   have byte4 := NHY_ZeroStep.read b 4#usize (by change 4<b.val.length;omega)
   have byte5 := NHY_ZeroStep.read b 5#usize (by change 5<b.val.length;omega)
   have reserve := NHY_SliceRead.read b 6#usize 8#usize (by decide) (by change 8≤b.val.length;omega)
   have read1 := NHY_SliceRead.read b 8#usize 40#usize (by decide) (by change 40≤b.val.length;omega)
   have read2 := NHY_SliceRead.read b 40#usize 72#usize (by decide) (by change 72≤b.val.length;omega)
   have read3 := NHY_SliceRead.read b 72#usize 104#usize (by decide) (by change 104≤b.val.length;omega)
   have cast1 := NHY_ExactArray.cast 32#usize (NHY_SliceRead.segment b 8 32) (record b len).registry_program rfl
   have cast2 := NHY_ExactArray.cast 32#usize (NHY_SliceRead.segment b 40 32) (record b len).registry_authority rfl
   have cast3 := NHY_ExactArray.cast 32#usize (NHY_SliceRead.segment b 72 32) (record b len).policy_binding rfl
   simp only [raw,NJI_Extracted.aspis_statement.pool_v1.format.decode_verifier_policy_v1,
    count,version,size,show (104#usize != 104#usize)=false from rfl,Bool.false_eq_true,ite_false,pre,byte4,byte5,reserve,read1,read2,read3,
    cast1,cast2,cast3,NJI_StdNe.value,lift,bind_tc_ok]
   simp only [NHY_SliceRead.segment,List.drop_zero,show (2#usize).val=2 from rfl,show (4#usize).val=4 from rfl,
    show (5#usize).val=5 from rfl,show (6#usize).val=6 from rfl,show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,show (72#usize).val=72 from rfl,
    show (104#usize).val=104 from rfl,Array.repeat,Array.to_slice,
    decide_eq_true_eq]
   by_cases gm : b.val.take 4=magic.val
   · simp only [gm,ite_true,not_true_eq_false,ite_false]
     by_cases gv : NHY_ZeroStep.byte b 4=1#u8
     · simp only [gv,show (1#u8 != 1#u8)=false from rfl,Bool.false_eq_true,ite_false,ite_true]
       by_cases gz : (b.val.drop 6).take 2=List.replicate 2 0#u8
       · simp only [gz,ite_true,not_true_eq_false,ite_false]
         dsimp only [NHY_SliceRead.segment] at cast1 cast2 cast3
         simp only [ne_self_iff_false,ite_false,show (2#usize).val=2 from rfl,cast1,cast2,cast3,bind_tc_ok,core.result.Result.unwrap]
         change (do let reply ← validator (record b len)
                    let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
                    match cf with
                    | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok (record b len))
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual P
                       (core.convert.FromSame F) residual) = _
         cases h : validator (record b len) with
         | fail e => simp [h]
         | div => simp [h]
         | ok r => cases r <;> rfl
       · simp_all
     · simp [gv]
   · simp [gm]
 · rename_i len
   have size : Slice.len b≠104#usize := by intro eq;exact len (congrArg UScalar.val eq)
   simp [raw,NJI_Extracted.aspis_statement.pool_v1.format.decode_verifier_policy_v1,count,size]

#print source
#print axioms source
end NJI_PolicyParser
