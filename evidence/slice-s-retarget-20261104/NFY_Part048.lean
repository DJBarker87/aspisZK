import Lean
import Aeneas
import S2W_D189Wrappers
import CPH_Program
import NFY_Part047
import AdapterRwModel

-- BEGIN copied JHb_DataRequest: lean/JHb_DataRequest.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHb_DataRequest
open Aeneas Aeneas.Std
def c00 : List U8 := [65#u8,83#u8,81#u8,56#u8,1#u8,1#u8,1#u8,0#u8,87#u8,148#u8,115#u8,19#u8,210#u8,50#u8,100#u8,26#u8,216#u8,21#u8,125#u8,102#u8,191#u8,175#u8,250#u8,177#u8,30#u8,76#u8,58#u8,153#u8,51#u8,29#u8,24#u8,244#u8]
theorem c00_length : c00.length=32 := by simp only [c00,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c00_length
def c01 : List U8 := [75#u8,250#u8,202#u8,182#u8,137#u8,151#u8,55#u8,211#u8,226#u8,148#u8,175#u8,188#u8,20#u8,239#u8,106#u8,254#u8,118#u8,184#u8,71#u8,222#u8,244#u8,68#u8,82#u8,248#u8,76#u8,195#u8,114#u8,128#u8,100#u8,101#u8,118#u8,7#u8]
theorem c01_length : c01.length=32 := by simp only [c01,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c01_length
def c02 : List U8 := [181#u8,68#u8,165#u8,57#u8,202#u8,155#u8,50#u8,58#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8]
theorem c02_length : c02.length=32 := by simp only [c02,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c02_length
def c03 : List U8 := [65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,65#u8,83#u8,67#u8,80#u8,1#u8,1#u8,1#u8,0#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8]
theorem c03_length : c03.length=32 := by simp only [c03,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c03_length
def c04 : List U8 := [55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8]
theorem c04_length : c04.length=32 := by simp only [c04,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c04_length
def c05 : List U8 := [5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,85#u8,246#u8,62#u8,4#u8,159#u8,80#u8,117#u8,33#u8]
theorem c05_length : c05.length=32 := by simp only [c05,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c05_length
def c06 : List U8 := [221#u8,239#u8,128#u8,120#u8,216#u8,131#u8,141#u8,49#u8,99#u8,239#u8,102#u8,35#u8,253#u8,148#u8,147#u8,6#u8,128#u8,120#u8,67#u8,103#u8,86#u8,177#u8,157#u8,56#u8,219#u8,27#u8,130#u8,0#u8,76#u8,144#u8,137#u8,6#u8]
theorem c06_length : c06.length=32 := by simp only [c06,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c06_length
def c07 : List U8 := [20#u8,96#u8,178#u8,97#u8,164#u8,37#u8,6#u8,0#u8,128#u8,143#u8,218#u8,112#u8,162#u8,164#u8,176#u8,20#u8,25#u8,186#u8,192#u8,19#u8,209#u8,175#u8,110#u8,117#u8,77#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c07_length : c07.length=32 := by simp only [c07,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c07_length
def c08 : List U8 := [38#u8,95#u8,6#u8,86#u8,21#u8,144#u8,64#u8,23#u8,144#u8,38#u8,14#u8,44#u8,19#u8,44#u8,204#u8,114#u8,34#u8,164#u8,10#u8,25#u8,49#u8,167#u8,186#u8,47#u8,31#u8,240#u8,152#u8,56#u8,72#u8,124#u8,118#u8,4#u8]
theorem c08_length : c08.length=32 := by simp only [c08,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c08_length
def c09 : List U8 := [35#u8,21#u8,136#u8,6#u8,65#u8,19#u8,78#u8,120#u8,113#u8,38#u8,13#u8,70#u8,250#u8,49#u8,224#u8,32#u8,8#u8,134#u8,48#u8,23#u8,1#u8,83#u8,145#u8,33#u8,35#u8,192#u8,81#u8,85#u8,205#u8,25#u8,236#u8,20#u8]
theorem c09_length : c09.length=32 := by simp only [c09,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c09_length
def bytes : List U8 := c00 ++ c01 ++ c02 ++ c03 ++ c04 ++ c05 ++ c06 ++ c07 ++ c08 ++ c09
theorem length : bytes.length=320 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length,c06_length,c07_length,c08_length,c09_length]
#print axioms length
def value : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩
end AspisR1.NFY_JHb_DataRequest
-- END copied JHb_DataRequest
-- BEGIN copied JGx_SdkContinuation: lean/JGx_SdkContinuation.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_SdkContinuation
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def afterValidation (ops : Ops) (accounts : S2W_ExtractionBoundary.Accounts)
    (validated : r1_pool_adapter.ValidatedAsqa) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let oa ← Slice.index_usize accounts 0#usize
  let r1 ← (r1_pool_adapter.owned.OwnedAccount.data ops) oa
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let oa1 ← Slice.index_usize accounts 6#usize
    let r2 ← (r1_pool_adapter.owned.OwnedAccount.data ops) oa1
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val2 =>
      let proof_start ←
        (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
      let o1 ← lift (Usize.checked_add proof_start validated.proof_length)
      let r3 ←
        core.option.Option.ok_or o1
          solana_program_error.ProgramError.InvalidAccountData
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let i1 := Slice.len val1
        if i1 != val3
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else
          let r4 ←
            ops.op22
              validated.statement
          let r5 ←
            core.result.Result.map_err
              r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
              r4 ()
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let s1 ← lift (Array.to_slice val4)
            let i2 := Slice.len s1
            let i3 ←
              (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
            if i2 != i3
            then
              ok (core.result.Result.Err
                solana_program_error.ProgramError.InvalidInstructionData)
            else
              let s2 ← lift (Array.to_slice val4)
              let s3 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                  val1 { start := proof_start, «end» := val3 }
              let o2 ← (observer ops)
              let r6 ←
                ops.op11
                  (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) s2 s3 val2
                  () o2
              let r7 ←
                core.result.Result.map_err (BuiltinFnOnce
                  aspis_r1_cost_probe.verifier.Error
                  solana_program_error.ProgramError) r6 (ops.op44)
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                ops.op53 validated.statement
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame
                  solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame
              solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame solana_program_error.ProgramError)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError)
      residual

#print axioms afterValidation
end AspisR1.NFY_JGx_SdkContinuation
end
-- END copied JGx_SdkContinuation
-- BEGIN copied JGx_SdkAfterValidationEq: lean/JGx_SdkAfterValidationEq.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_SdkAfterValidationEq
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot)
    (validated : r1_pool_adapter.ValidatedAsqa)
    (count : Slice.len accounts=7#usize)
    (magic : (do
      let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end»:=4#usize}
      let s ← core.array.Array.index (core.ops.index.IndexSlice
        ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC ()
      core.cmp.PartialEq.ne.trait_default ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) o (some s))=ok false)
    (validation : r1_pool_adapter.owned.validate_asq8 ops program accounts data slot=ok (.Ok validated)) :
    r1_pool_adapter.owned.stage2_owned ops program accounts data slot=
      NFY_JGx_SdkContinuation.afterValidation ops accounts validated := by
  unfold r1_pool_adapter.owned.stage2_owned
  rw [count]
  simp only [show (7#usize !=7#usize)=false from by decide,Bool.false_eq_true,ite_false]
  obtain ⟨o,read,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ magic
  obtain ⟨s,index,neq⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  rw [read,bind_tc_ok,index,bind_tc_ok,neq,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [validation,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.NFY_JGx_SdkAfterValidationEq
end
-- END copied JGx_SdkAfterValidationEq
-- BEGIN copied JGx_MagicGate: lean/JGx_MagicGate.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_MagicGate
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def value (ops : Ops) (data : Slice U8) : Result Bool := do
  let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end»:=4#usize}
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC ()
  core.cmp.PartialEq.ne.trait_default ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
    (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) o (some s)

theorem source (ops : Ops) (data : Slice U8) (selected : Option (Slice U8)) (magic : Slice U8)
    (read : core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end»:=4#usize}=ok selected)
    (array : core.array.Array.index (core.ops.index.IndexSlice
      ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
      aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC ()=ok magic)
    (compare : core.cmp.PartialEq.ne.trait_default ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
      (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) selected (some magic)=ok false) :
    value ops data=ok false := by
  unfold value
  rw [read,bind_tc_ok,array,bind_tc_ok,compare]
#print axioms source
end AspisR1.NFY_JGx_MagicGate
end
-- END copied JGx_MagicGate
-- BEGIN copied JGx_RequestBytes: lean/JGx_RequestBytes.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_RequestBytes
open Aeneas Aeneas.Std Result

def magic : Slice U8 := ⟨[65#u8,83#u8,81#u8,56#u8],by simp;scalar_tac⟩
def value (payload : Array U8 316#usize) : Slice U8 :=
  ⟨magic.val++payload.val,by simp only [List.length_append,magic,List.length_cons,List.length_nil,payload.property];scalar_tac⟩

theorem length (payload : Array U8 316#usize) : Slice.len (value payload)=320#usize := by
  apply UScalar.eq_of_val_eq
  change (magic.val++payload.val).length=320
  rw [List.length_append,payload.property]
  rfl
#print axioms length

theorem first (payload : Array U8 316#usize) :
    (value payload).val.take 4=magic.val := by
  change (magic.val++payload.val).take 4=magic.val
  have size : magic.val.length=4 := rfl
  have h : (magic.val++payload.val).take magic.val.length=magic.val := List.take_left
  simpa only [size] using h
#print axioms first
end AspisR1.NFY_JGx_RequestBytes
end
-- END copied JGx_RequestBytes
-- BEGIN copied JGx_RequestRead: lean/JGx_RequestRead.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_RequestRead
open Aeneas Aeneas.Std Result

#print core.slice.index.SliceIndexRangeToUsizeSlice.get
theorem source (payload : Array U8 316#usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (NFY_JGx_RequestBytes.value payload) {«end»:=4#usize}=ok (some NFY_JGx_RequestBytes.magic) := by
  unfold core.slice.Slice.get
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice]
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.get
  have hlen : (NFY_JGx_RequestBytes.value payload).length=320 := congrArg UScalar.val (NFY_JGx_RequestBytes.length payload)
  rw [if_pos (by change 4≤(NFY_JGx_RequestBytes.value payload).length;rw [hlen];decide)]
  apply congrArg ok
  apply congrArg some
  apply Subtype.ext
  exact NFY_JGx_RequestBytes.first payload

#print axioms source
end AspisR1.NFY_JGx_RequestRead
end
-- END copied JGx_RequestRead
-- BEGIN copied JGx_MagicStd: lean/JGx_MagicStd.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_MagicStd
open Aeneas Aeneas.Std Result

def optionEq {T : Type} (cmp : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left,right with
  | none,none=>ok true
  | some x,some y=>cmp.eq x y
  | _,_=>ok false

def install (ops : AdapterRw.Ops) : AdapterRw.Ops :=
  {ops with op2:=optionEq,op4:=fun _ input=>ok input}

theorem source (ops : AdapterRw.Ops) (payload : Array U8 316#usize) :
    NFY_JGx_MagicGate.value (install ops) (NFY_JGx_RequestBytes.value payload)=ok false := by
  unfold NFY_JGx_MagicGate.value
  rw [NFY_JGx_RequestRead.source,bind_tc_ok]
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
  rfl
#print axioms source
end AspisR1.NFY_JGx_MagicStd
end
-- END copied JGx_MagicStd
-- BEGIN copied JHb_RequestCarrier: lean/JHb_RequestCarrier.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHb_RequestCarrier
open Aeneas Aeneas.Std Result

def payload : Array U8 316#usize := ⟨NFY_JHb_DataRequest.bytes.drop 4,by
  rw [List.length_drop,NFY_JHb_DataRequest.length]
  rfl⟩

theorem same : NFY_JGx_RequestBytes.value payload=NFY_JHb_DataRequest.value := by
  apply Subtype.ext
  change NFY_JGx_RequestBytes.magic.val ++ NFY_JHb_DataRequest.bytes.drop 4=NFY_JHb_DataRequest.bytes
  have header : NFY_JHb_DataRequest.bytes.take 4=NFY_JGx_RequestBytes.magic.val := rfl
  rw [← header]
  exact List.take_append_drop 4 NFY_JHb_DataRequest.bytes
#print axioms same

theorem magic (base : AdapterRw.Ops) :
    NFY_JGx_MagicGate.value (NFY_JGx_MagicStd.install base) NFY_JHb_DataRequest.value=ok false := by
  rw [← same]
  exact NFY_JGx_MagicStd.source base payload
#print axioms magic

theorem length : Slice.len NFY_JHb_DataRequest.value=320#usize := by
  rw [← same]
  exact NFY_JGx_RequestBytes.length payload
#print axioms length
end AspisR1.NFY_JHb_RequestCarrier
end
-- END copied JHb_RequestCarrier
-- BEGIN copied JHb_Programs: lean/JHb_Programs.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHb_Programs
open Aeneas Aeneas.Std
/-- Default frozen source slot, r1_pool_adapter.rs AUDIT_POOL_PROGRAM fallback.
IDa leaves this slot in missing.adapter; this is an explicit fixture choice. -/
def pool : S2W_ExtractionBoundary.Program := Array.repeat 32#usize 65#u8
def registry : S2W_ExtractionBoundary.Program := Array.repeat 32#usize 68#u8
def foreign : S2W_ExtractionBoundary.Program := Array.repeat 32#usize 85#u8

theorem pool_ne_verifier : pool ≠ CPH_Program.verifier := by
  intro h
  have hd := congrArg (fun k : S2W_ExtractionBoundary.Program => k.val[0]?) h
  change some (65#u8) = some (95#u8) at hd
  exact (by decide : (65#u8) ≠ 95#u8) (Option.some.inj hd)
#print axioms pool_ne_verifier
end AspisR1.NFY_JHb_Programs
end
-- END copied JHb_Programs
-- BEGIN copied JHb_RequestBindings: lean/JHb_RequestBindings.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHb_RequestBindings
open Aeneas Aeneas.Std Result

theorem profile : (NFY_JHb_DataRequest.bytes.drop 8).take 32=AdapterRw.r1_pool_adapter.PROFILE_BINDING.val := by
  unfold AdapterRw.r1_pool_adapter.PROFILE_BINDING
  rfl
#print axioms profile

theorem release : (NFY_JHb_DataRequest.bytes.drop 40).take 32=AdapterRw.r1_pool_adapter.RELEASE_BINDING.val := by
  unfold AdapterRw.r1_pool_adapter.RELEASE_BINDING
  rfl
#print axioms release

theorem pool : (NFY_JHb_DataRequest.bytes.drop 72).take 32=NFY_JHb_Programs.pool.val := by rfl
#print axioms pool

theorem header : NFY_JHb_DataRequest.bytes.take 8=[65#u8,83#u8,81#u8,56#u8,1#u8,1#u8,1#u8,0#u8] := by rfl
#print axioms header
end AspisR1.NFY_JHb_RequestBindings
end
-- END copied JHb_RequestBindings
-- BEGIN copied JHd_RequestValue: lean/JHd_RequestValue.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestValue
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.pair_forest_terminal

def value : PoolV1PairForestTerminalRequestV1 :=
  ⟨AdapterRw.r1_pool_adapter.PROFILE_BINDING,AdapterRw.r1_pool_adapter.RELEASE_BINDING,
    NFY_JHb_Programs.pool,.PrivateTransfer NFY_JHd_RequestPayment.value⟩

theorem profile_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    value.verifier_profile (Array.repeat 32#usize 0#u8)=ok false := by
  unfold value AdapterRw.r1_pool_adapter.PROFILE_BINDING
  rfl
#print axioms profile_nonzero

theorem release_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    value.verifier_release (Array.repeat 32#usize 0#u8)=ok false := by
  unfold value AdapterRw.r1_pool_adapter.RELEASE_BINDING
  rfl
#print axioms release_nonzero

theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    value.pool_program (Array.repeat 32#usize 0#u8)=ok false := by rfl
#print axioms pool_nonzero
end AspisR1.NFY_JHd_RequestValue
-- END copied JHd_RequestValue
-- BEGIN copied JHd_RequestCarrier: lean/JHd_RequestCarrier.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestCarrier
open Aeneas Aeneas.Std Result

def mapPoolV1PaymentStatementFormatError (e : AspisR20Request.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongTransitionKind=>.WrongTransitionKind
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .NonZeroReserved=>.NonZeroReserved
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .InvalidAnchorSequence=>.InvalidAnchorSequence
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .NonCanonicalAssetId=>.NonCanonicalAssetId
  | .InvalidWithdrawalAmount=>.InvalidWithdrawalAmount
  | .InvalidDestination=>.InvalidDestination
  | .InvalidEnvelope=>.InvalidEnvelope
  | .EnvelopeMismatch=>.EnvelopeMismatch
#print axioms mapPoolV1PaymentStatementFormatError

def mapPoolV1TreeError (e : AspisR20Request.pool_v1.incremental_merkle.PoolV1TreeError) : AdapterRw.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError :=
  match e with
  | .TreeFull=>.TreeFull
  | .InsufficientCapacity=>.InsufficientCapacity
  | .IndexOutOfRange=>.IndexOutOfRange
  | .RootMismatch=>.RootMismatch
  | .NonCanonicalFrontier=>.NonCanonicalFrontier
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongDepth=>.WrongDepth
  | .WrongTreeHash=>.WrongTreeHash
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .NonZeroReserved=>.NonZeroReserved
#print axioms mapPoolV1TreeError

def mapPoolV1PairForestAccountErrorV1 (e : AspisR20Request.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongLaneCount=>.WrongLaneCount
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .WrongDepth=>.WrongDepth
  | .WrongFormatBinding=>.WrongFormatBinding
  | .NonZeroReserved=>.NonZeroReserved
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .InvalidBoolean=>.InvalidBoolean
  | .InvalidMasterState=>.InvalidMasterState
  | .InvalidLane=>.InvalidLane
  | .LaneMasterMismatch=>.LaneMasterMismatch
  | .LaneOrderMismatch=>.LaneOrderMismatch
  | .LaneSequenceDecreased=>.LaneSequenceDecreased
  | .DuplicateCheckpoint=>.DuplicateCheckpoint
  | .CheckpointSequenceOverflow=>.CheckpointSequenceOverflow
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .Identity=>.Identity
  | .Policy=>.Policy
  | .Tree x=>.Tree (mapPoolV1TreeError x)
#print axioms mapPoolV1PairForestAccountErrorV1

def mapPoolV1PairLiveSnapshotErrorV1 (e : AspisR20Request.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongFormatBinding=>.WrongFormatBinding
  | .NonZeroReserved=>.NonZeroReserved
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .SequenceIndexMismatch=>.SequenceIndexMismatch
  | .TreeFull=>.TreeFull
  | .NonCanonicalDigest=>.NonCanonicalDigest
#print axioms mapPoolV1PairLiveSnapshotErrorV1

def mapPoolV1PairVerifierTransportErrorV1 (e : AspisR20Request.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongStatementVersion=>.WrongStatementVersion
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .InvalidTransitionKind=>.InvalidTransitionKind
  | .WrongSuccessCode=>.WrongSuccessCode
  | .WrongPairFormat=>.WrongPairFormat
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .InvalidProofBodyLength=>.InvalidProofBodyLength
  | .InvalidStatementPayloadLength=>.InvalidStatementPayloadLength
  | .InvalidLiveSnapshotPayloadLength=>.InvalidLiveSnapshotPayloadLength
  | .NonCanonicalOutputPair=>.NonCanonicalOutputPair
  | .InvalidAfterstateIndex=>.InvalidAfterstateIndex
  | .NonCanonicalAfterstate=>.NonCanonicalAfterstate
#print axioms mapPoolV1PairVerifierTransportErrorV1

def mapPoolV1PairLatePublicStatementErrorV1 (e : AspisR20Request.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongItemCount=>.WrongItemCount
  | .WrongHeaderLength=>.WrongHeaderLength
  | .WrongSnapshotLength=>.WrongSnapshotLength
  | .WrongAfterstateLength=>.WrongAfterstateLength
  | .WrongTotalLength=>.WrongTotalLength
  | .NonZeroReserved=>.NonZeroReserved
  | .Snapshot x=>.Snapshot (mapPoolV1PairLiveSnapshotErrorV1 x)
  | .Afterstate x=>.Afterstate (mapPoolV1PairVerifierTransportErrorV1 x)
  | .AfterstateIndexMismatch=>.AfterstateIndexMismatch
#print axioms mapPoolV1PairLatePublicStatementErrorV1

def mapPoolV1PairForestTerminalFormatErrorV1 (e : AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .InvalidTransitionKind=>.InvalidTransitionKind
  | .InvalidOutputLane=>.InvalidOutputLane
  | .NonZeroBinding=>.NonZeroBinding
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .OutputLaneMismatch=>.OutputLaneMismatch
  | .MasterBindingMismatch=>.MasterBindingMismatch
  | .DeploymentBindingMismatch=>.DeploymentBindingMismatch
  | .HistoricalAnchorMismatch=>.HistoricalAnchorMismatch
  | .CheckpointBindingMismatch=>.CheckpointBindingMismatch
  | .SelectedLaneBindingMismatch=>.SelectedLaneBindingMismatch
  | .LiveSnapshotMismatch=>.LiveSnapshotMismatch
  | .CandidateAfterstateMismatch=>.CandidateAfterstateMismatch
  | .ResultBindingMismatch=>.ResultBindingMismatch
  | .WithdrawalDestinationMismatch=>.WithdrawalDestinationMismatch
  | .Payment x=>.Payment (mapPoolV1PaymentStatementFormatError x)
  | .LaneTransition x=>.LaneTransition (mapPoolV1PairLatePublicStatementErrorV1 x)
  | .Afterstate x=>.Afterstate (mapPoolV1PairVerifierTransportErrorV1 x)
  | .Account x=>.Account (mapPoolV1PairForestAccountErrorV1 x)
#print axioms mapPoolV1PairForestTerminalFormatErrorV1

def privateTransfer (p : AspisR20Request.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩

def withdrawal (p : AspisR20Request.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩

def payment (p : AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1) :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1 :=
  match p with
  | .PrivateTransfer p=>.PrivateTransfer (privateTransfer p)
  | .Withdrawal p=>.Withdrawal (withdrawal p)

def request (p : AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1) :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 :=
  ⟨p.verifier_profile,p.verifier_release,p.pool_program,payment p.«public»⟩

def actual := request NFY_JHd_RequestValue.value

theorem profile : actual.verifier_profile=AdapterRw.r1_pool_adapter.PROFILE_BINDING := rfl
theorem release : actual.verifier_release=AdapterRw.r1_pool_adapter.RELEASE_BINDING := rfl
theorem pool : actual.pool_program=NFY_JHb_Programs.pool := rfl
#print axioms profile
#print axioms release
#print axioms pool
end AspisR1.NFY_JHd_RequestCarrier
-- END copied JHd_RequestCarrier

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
