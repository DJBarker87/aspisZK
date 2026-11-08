import NNH_RSLReads
import NNH_ValidateEval
import NNH_Libraries
import NNH_OptionOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Weak241Prefix
open RSL RSL.TX2_241 NMS_RSLRefine NMS_RSLStepFacts
open NND_Returned NNH_Libraries
/-- The actual weak reference's prefix, stopped before any canonical auth
value is demanded. It carries the SAME validation, encoding and read cuts. -/
structure Packet (V : V2Lib) (a : Args) (env : Env) where
 reads : NNH_RSLReads.Cut V a env
 validated : TX2_242.Validated L
 validate_ok : NNH_ValidateEval.value L D LIBB_PoolLib.values
  ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env = .ok validated
 n_eq : reads.n = validated.proof_length
 encode_ok : LIBB_PoolLib.values.encode validated.statement env = some reads.publicBytes
 guards : (a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC) = false
 end_bound : AFTERSTATE_BYTES+reads.n < USIZE_LIMIT

theorem produce (V : V2Lib) (a : Args) (env : Env) (events : List Event)
 (run : Ref L D V a env ⟨.ret (.ok ()),events⟩) : Nonempty (Packet V a env) := by
 unfold Ref at run
 obtain ⟨u,_,_,guard,h,_⟩ := rsbind_return _ _ _ _ _ run
 have guards := check_return _ _ _ _ guard
 have passed := guards
 simp only [Bool.or_eq_false_iff] at passed
 have count : a.accounts.length=7 := by simpa using passed.1.1
 obtain ⟨validated,ve,_,vcall,h,_⟩ := rsbind_return _ _ _ _ _ h
 have validate_ok := (NNH_ValidateEval.returned L D LIBB_PoolLib.values
  ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env
  ⟨.ret (.ok validated),ve⟩ (.ok validated) vcall.2 rfl).symm
 obtain ⟨acc0,_,_,index0,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨proofData,_,_,read0,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨acc6,_,_,index6,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨checkpointData,_,_,read6,h,_⟩ := rsbind_return _ _ _ _ _ h
 obtain ⟨_,_,_,endGuard,h,_⟩ := rsbind_return _ _ _ _ _ h
 have bound : AFTERSTATE_BYTES+validated.proof_length < USIZE_LIMIT := by
  have chk := check_return _ _ _ _ endGuard
  simpa only [decide_eq_false_iff_not,not_le] using chk
 obtain ⟨_,_,_,lengthGuard,h,_⟩ := rsbind_return _ _ _ _ _ h
 have proofLength : proofData.length=AFTERSTATE_BYTES+validated.proof_length := by
  simpa using check_return _ _ _ _ lengthGuard
 obtain ⟨encoded,ee,_,encoding,h,_⟩ := rsbind_return _ _ _ _ _ h
 have encValue : encoded = LIBB_PoolLib.values.encode validated.statement env :=
  Except.ok.inj ((NND_Returned.rs_lift _ env _ (LIBB_PoolLib.values.encode_ret _ env))
   ⟨.ret (.ok encoded),ee⟩ (.ok encoded) encoding rfl)
 obtain ⟨publicBytes,oe,_,optionCall,h,_⟩ := rsbind_return _ _ _ _ _ h
 have optionValue := (NND_Returned.ofOption env encoded .invalidInstructionData
  ⟨.ret (.ok publicBytes),oe⟩ (.ok publicBytes) optionCall rfl).symm
 have encode_ok : LIBB_PoolLib.values.encode validated.statement env = some publicBytes := by
  rw [←encValue]
  exact NNH_OptionOk.value _ _ _ optionValue
 obtain ⟨_,_,_,publicGuard,h,_⟩ := rsbind_return _ _ _ _ _ h
 have publicLength : publicBytes.length=STATEMENT_BYTES := by simpa using check_return _ _ _ _ publicGuard
 obtain ⟨verifyEvents,domain,verified⟩ := NNH_RSLAuth.call V publicBytes
  (slice proofData AFTERSTATE_BYTES (AFTERSTATE_BYTES+validated.proof_length)) checkpointData
  (L.emitResult validated.statement) env _ h
 exact ⟨{
  reads := {
   acc0 := acc0,acc6 := acc6,proofData := proofData,checkpointData := checkpointData,
   publicBytes := publicBytes,n := validated.proof_length,verifyEvents := verifyEvents,
   count := count,index0 := index_return _ _ _ _ _ index0,index6 := index_return _ _ _ _ _ index6,
   read0 := NNH_Rev2Support.data_return _ _ _ _ read0,
   read6 := NNH_Rev2Support.data_return _ _ _ _ read6,
   proofLength := proofLength,publicLength := publicLength,domain := domain,verified := verified }
  validated := validated,validate_ok := validate_ok,n_eq := rfl,encode_ok := encode_ok,
  guards := guards,end_bound := bound }⟩
#print axioms produce
end AspisR1.NNH_Weak241Prefix
end
