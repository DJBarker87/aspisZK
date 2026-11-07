import NMX_R3_LanePort
set_option autoImplicit false
namespace NMX_R3_LaneAllocation
open RSL

/-- Aeneas erases the final Box. This restores that one source allocation site,
including its silent abort. No prior rejection arm allocates. -/
def emitted (b : Bytes) : RS LaneState :=
 match NMX_R3_LanePort.pureResult b with
 | none => RS.throw .invalidAccountData
 | some a => RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure a)

theorem reference_eq (b : Bytes) : emitted b = TX2_217.Ref b := by
 unfold emitted
 rw [NMX_R3_LanePort.pure_eq]
 rfl

theorem observations (b : Bytes) (env : Env) (o : Obs (Except ProgramError LaneState)) :
 emitted b env o ↔ match NMX_R3_LanePort.pureResult b with
 | none => o = ⟨.ret (.error .invalidAccountData),[]⟩
 | some a => o = ⟨.ret (.ok a),[]⟩ ∨ o = ⟨.abort,[]⟩ := by
 unfold emitted
 cases NMX_R3_LanePort.pureResult b with
 | none => rfl
 | some a => exact RS.alloc_seq_iff (RS.pure a) env o

def realize (allocationSucceeded : Bool) (b : Bytes) (_env : Env) :
 Obs (Except ProgramError LaneState) :=
 match NMX_R3_LanePort.pureResult b with
 | none => ⟨.ret (.error .invalidAccountData),[]⟩
 | some a => if allocationSucceeded then ⟨.ret (.ok a),[]⟩ else ⟨.abort,[]⟩

/-- Full emitted-reference RowSpec with either allocation outcome, every input
length and every decoder Result. Native correspondence is a separate gate. -/
theorem root (allocationSucceeded : Bool) : TX2_217.RowSpec_217 (realize allocationSucceeded) := by
 intro b env _
 rw [←reference_eq b, observations]
 cases h : NMX_R3_LanePort.pureResult b <;> cases allocationSucceeded <;>
  simp only [realize,h,Bool.false_eq_true,↓reduceIte,or_true,Or.inl,eq_self]

/-- No abort or return observation is lost by the allocation interpretation. -/
theorem complete (b : Bytes) (env : Env) (o : Obs (Except ProgramError LaneState)) :
 TX2_217.Ref b env o ↔ ∃ allocationSucceeded : Bool, o = realize allocationSucceeded b env := by
 rw [←reference_eq b, observations]
 cases h : NMX_R3_LanePort.pureResult b with
 | none => simp only [realize,h,exists_const]
 | some a => simp only [realize,h,Bool.exists_bool,↓reduceIte]; exact or_comm
#print axioms reference_eq
#print axioms observations
#print axioms root
#print axioms complete
end NMX_R3_LaneAllocation
