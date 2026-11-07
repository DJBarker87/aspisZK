import NMX_R3_NativeWindow
import NMX_R3_NativeFrame
set_option autoImplicit false
namespace NMX_R3_DecoderFold
open RSL
attribute [local irreducible] TX2_217.frontierLoop TX2_217.decodeDigestCanonical

/-- Source-ordered pure control flow after installing the native predicate and
same-window child packets. Native packet provenance is external P6 evidence;
this definition itself makes no claim to be an Aeneas extraction of the frozen
body (that extraction failed). -/
def source (b : Bytes) : Option LaneState :=
 if b.length != LANE_ACCOUNT_BYTES then none else NMX_R3_LaneModels.header b

/-- Source prefix, recursive frontier and return continuation composed against
exactly the emitted primary reference, including every nonexpected length. -/
theorem source_eq_reference (b : Bytes) : source b = NMX_R3_LanePort.pureResult b := by
 rw [NMX_R3_LanePort.pure_eq]
 unfold source
 split
 · rename_i wrong
   have bad : TX2_217.headerBad b = true := by
    simp only [TX2_217.headerBad,wrong,Bool.true_or]
   simp only [TX2_217.laneDecode,bad,↓reduceIte]
 · rename_i passed
   have extent : b.length = 768 := by
    change b.length = LANE_ACCOUNT_BYTES
    simpa only [bne_iff_ne,not_not] using passed
   exact NMX_R3_LaneModelEquality.value b extent

/-- Runtime choice is pointwise in the input and environment, not one global
allocation assumption and not a requirement that allocation succeeds. -/
def decode (allocationSucceeded : Bytes → Env → Bool) (b : Bytes) (env : Env) :
 Obs (Except ProgramError LaneState) :=
 match source b with
 | none => ⟨.ret (.error .invalidAccountData),[]⟩
 | some a => if allocationSucceeded b env then ⟨.ret (.ok a),[]⟩ else ⟨.abort,[]⟩

theorem decode_eq (allocationSucceeded : Bytes → Env → Bool) (b : Bytes) (env : Env) :
 decode allocationSucceeded b env =
 NMX_R3_LaneAllocation.realize (allocationSucceeded b env) b env := by
 unfold decode
 rw [source_eq_reference]
 unfold NMX_R3_LaneAllocation.realize
 generalize NMX_R3_LanePort.pureResult b = model
 cases model <;> rfl
#print axioms decode_eq

theorem root (allocationSucceeded : Bytes → Env → Bool) :
 TX2_217.RowSpec_217 (decode allocationSucceeded) := by
 intro b env _
 have selected := NMX_R3_LaneAllocation.root (allocationSucceeded b env) b env trivial
 rw [decode_eq]
 exact selected

theorem complete (b : Bytes) (env : Env) (o : Obs (Except ProgramError LaneState)) :
 TX2_217.Ref b env o ↔ ∃ allocationSucceeded : Bool,
 o = decode (fun _ _ => allocationSucceeded) b env := by
 simpa only [decode_eq] using
  NMX_R3_LaneAllocation.complete b env o
#print axioms source_eq_reference
#print axioms root
#print axioms complete
end NMX_R3_DecoderFold
