import NKY_BoxCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_BoxTotal
open Aeneas Aeneas.Std Result
open NKY_BoxAction

/-- The observed carrier is used only if the SAME allocation returns. On
abort/exhaustion it is an unconstrained ghost, with no native-success premise. -/
def native {T F S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation)
 (raw : core.result.Result T F) (observed : Owned T) :
 Result (core.result.Result (Owned T) PE × S) :=
 match raw with
 | .Err _ => ok (.Err .InvalidAccountData,s)
 | .Ok _ => do
  let post ← a.allocate s bytes
  match r with
  | .Err _ => fail .panic
  | .Ok _ => ok (.Ok observed,post)

def Ready {T F S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (raw : core.result.Result T F) (observed : Owned T) : Prop :=
 match raw,a.allocate s bytes,r with
 | .Ok value,.ok _,.Ok _ => observed.owner=allocated ∧ observed.value=value
 | _,_,_ => True

def CheckpointWindows {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (allocated : Nat)
 (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF)
 (observed : Owned NJQ_Carrier.CC) : Prop :=
 match raw,a.allocate s 176,r with
 | .Ok value,.ok _,.Ok _ =>
   NKF_Windows.Checkpoint value observed.value ∧ observed.owner=allocated
 | _,_,_ => True

def MasterWindows {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (allocated : Nat)
 (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF)
 (observed : Owned NJQ_Carrier.CM) : Prop :=
 match raw,a.allocate s 304,r with
 | .Ok value,.ok _,.Ok _ =>
   NKF_Windows.Master value observed.value ∧ observed.owner=allocated
 | _,_,_ => True

theorem association {T F S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (bytes : Nat) (r : NP6_StdModel.Reservation) (allocated : Nat)
 (raw : core.result.Result T F) (observed : Owned T)
 (cut : Ready a s bytes r allocated raw observed) :
 native a s bytes r raw observed=
 run a s bytes r allocated (ok (NKF_BoxModel.tail raw)) := by
 cases raw with
 | Err e => rfl
 | Ok value =>
  cases ha:a.allocate s bytes with
  | fail e => simp [native,run,newBox,NKF_BoxModel.tail,ha]
  | div => simp [native,run,newBox,NKF_BoxModel.tail,ha]
  | ok post =>
   cases r with
   | Err e => simp [native,run,newBox,NKF_BoxModel.tail,ha]
   | Ok unit =>
    cases unit
    have both : observed.owner=allocated ∧ observed.value=value := by simpa only [Ready,ha] using cut
    have same:=NKY_BoxFrame.carrier_identity observed allocated value both.1 both.2
    simp [native,run,newBox,NKF_BoxModel.tail,ha,same]

theorem checkpoint_ready {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (allocated : Nat)
 (raw : core.result.Result NJQ_Carrier.CC NJQ_Carrier.CF) (observed : Owned NJQ_Carrier.CC)
 (cut : CheckpointWindows a s r allocated raw observed) :
 Ready a s 176 r allocated raw observed := by
 cases raw with
 | Err e => trivial
 | Ok value =>
  cases ha:a.allocate s 176 <;> cases r <;> simp only [Ready,ha] <;> try trivial
  have h : NKF_Windows.Checkpoint value observed.value ∧ observed.owner=allocated := by
   simpa only [CheckpointWindows,ha] using cut
  exact ⟨h.2,(NKF_BoxFields.checkpoint _ _ (NKF_Windows.checkpoint_fields _ _ h.1)).symm⟩

theorem master_ready {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (r : NP6_StdModel.Reservation) (allocated : Nat)
 (raw : core.result.Result NJQ_Carrier.CM NJQ_Carrier.CF) (observed : Owned NJQ_Carrier.CM)
 (cut : MasterWindows a s r allocated raw observed) :
 Ready a s 304 r allocated raw observed := by
 cases raw with
 | Err e => trivial
 | Ok value =>
  cases ha:a.allocate s 304 <;> cases r <;> simp only [Ready,ha] <;> try trivial
  have h : NKF_Windows.Master value observed.value ∧ observed.owner=allocated := by
   simpa only [MasterWindows,ha] using cut
  exact ⟨h.2,(NKF_BoxFields.master _ _ (NKF_Windows.master_fields _ _ h.1)).symm⟩

/-- TX2:216 total root. No observation of a returned Box is required on any
nonreturning allocation arm. The only parent hypothesis is its reviewed
returning field/pointer windows, and the CLOSED raw cut at SAME bytes. -/
theorem checkpoint {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (heap : NKY_BoxFrame.Heap NJQ_Carrier.CC) (r : NP6_StdModel.Reservation)
 (allocated : Nat) (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.C NJQ_Carrier.F)
 (observed : Owned NJQ_Carrier.CC) (decoder : NJQ_CheckpointTotal.Cut bytes raw)
 (cut : CheckpointWindows a s r allocated (NJQ_Carrier.checkpoint_result raw) observed) :
 native a s 176 r (NJQ_Carrier.checkpoint_result raw) observed=
 run a s 176 r allocated (NKF_CheckpointBox.reference bytes) ∧
 NKY_BoxPacket.Law a s 176 8 r allocated heap (NKF_CheckpointBox.reference bytes) := by
 have value : ok (NKF_BoxModel.tail (NJQ_Carrier.checkpoint_result raw))=NKF_CheckpointBox.reference bytes :=
  NKF_CheckpointBox.source bytes raw decoder _ rfl
 exact ⟨(association a s 176 r allocated _ observed (checkpoint_ready a s r allocated _ observed cut)).trans
  (congrArg (run a s 176 r allocated) value),NKY_BoxPacket.complete _ _ _ _ _ _ _ _⟩

theorem master {S : Type} (a : S2W_D189Wrappers.Allocator S) (s : S)
 (heap : NKY_BoxFrame.Heap NJQ_Carrier.CM) (r : NP6_StdModel.Reservation)
 (allocated : Nat) (bytes : Slice U8) (raw : core.result.Result NJQ_Carrier.M NJQ_Carrier.F)
 (observed : Owned NJQ_Carrier.CM) (decoder : NJQ_MasterTotal.Cut bytes raw)
 (cut : MasterWindows a s r allocated (NJQ_Carrier.master_result raw) observed) :
 native a s 304 r (NJQ_Carrier.master_result raw) observed=
 run a s 304 r allocated (NKF_MasterBox.reference bytes) ∧
 NKY_BoxPacket.Law a s 304 8 r allocated heap (NKF_MasterBox.reference bytes) := by
 have value : ok (NKF_BoxModel.tail (NJQ_Carrier.master_result raw))=NKF_MasterBox.reference bytes :=
  NKF_MasterBox.source bytes raw decoder _ rfl
 exact ⟨(association a s 304 r allocated _ observed (master_ready a s r allocated _ observed cut)).trans
  (congrArg (run a s 304 r allocated) value),NKY_BoxPacket.complete _ _ _ _ _ _ _ _⟩
#print axioms association
#print axioms checkpoint_ready
#print axioms master_ready
#print checkpoint
#print axioms checkpoint
#print master
#print axioms master
end AspisR1.NKY_BoxTotal
end
