import NCE_CountCuts

set_option autoImplicit false
namespace AspisR1.NCE_CountInitCuts

structure InitState (Frame : Type) where
  source : Nat → Nat
  memory : Nat → Nat
  cursor : Nat
  n : Nat
  frame : Frame

/-- Zero initialization is observed at one arbitrary coordinate of the
lifted finite native array. The representation is zero outside that array.
The caller frame/source/n are retained; no initialized count result. -/
def NCE_Native_CountZero {Frame : Type}
    (create : (Nat → Nat) → Nat → Frame → InitState Frame) : Prop :=
  ∀ source n frame, n ≤ 16 →
    (∀ k, (create source n frame).memory k = 0) ∧
    (∀ k, (create source n frame).source k = source k) ∧
    (create source n frame).cursor = 0 ∧ (create source n frame).n = n ∧
    (create source n frame).frame = frame

/-- ONE actual prefix-copy cell/window on the SAME private count array.
The source is immutable and every exterior coordinate is retained. Native
credit requires the exact KMX patch and matched failing copy control. -/
def NCE_Native_CountCopy {Frame : Type} (copy : InitState Frame → InitState Frame) : Prop :=
  ∀ s, s.cursor < s.n → s.n ≤ 16 →
    (∀ k, k < s.n → s.source k < 262144) →
    (∀ k, (copy s).memory k = if k = s.cursor then s.source s.cursor else s.memory k) ∧
    (∀ k, (copy s).source k = s.source k) ∧
    (copy s).cursor = s.cursor+1 ∧ (copy s).n = s.n ∧ (copy s).frame = s.frame

theorem create_eq {Frame : Type}
    (create : (Nat → Nat) → Nat → Frame → InitState Frame)
    (cut : NCE_Native_CountZero create) (source : Nat → Nat) (n : Nat) (frame : Frame)
    (small : n ≤ 16) : create source n frame = ⟨source,fun _ => 0,0,n,frame⟩ := by
  obtain ⟨mem,src,cursor,size,fr⟩ := cut source n frame small
  have memory : (create source n frame).memory = fun _ => 0 := funext mem
  have sourceEq : (create source n frame).source = source := funext src
  change InitState.mk (create source n frame).source (create source n frame).memory
    (create source n frame).cursor (create source n frame).n (create source n frame).frame = _
  congr 1 <;> first | exact sourceEq | exact memory | exact cursor | exact size | exact fr

theorem copy_eq {Frame : Type} (copy : InitState Frame → InitState Frame)
    (cut : NCE_Native_CountCopy copy) (s : InitState Frame)
    (active : s.cursor < s.n) (small : s.n ≤ 16)
    (range : ∀ k, k < s.n → s.source k < 262144) :
    copy s = {s with memory := KMX_CopyMeaning.write s.memory s.cursor (s.source s.cursor), cursor:=s.cursor+1} := by
  obtain ⟨mem,src,cursor,size,fr⟩ := cut s active small range
  have memory : (copy s).memory = KMX_CopyMeaning.write s.memory s.cursor (s.source s.cursor) := funext mem
  have sourceEq : (copy s).source = s.source := funext src
  change InitState.mk (copy s).source (copy s).memory (copy s).cursor (copy s).n (copy s).frame = _
  congr 1 <;> first | exact sourceEq | exact memory | exact cursor | exact size | exact fr

def run {Frame : Type} (copy : InitState Frame → InitState Frame) : Nat → InitState Frame → InitState Frame
  | 0,s => s
  | fuel+1,s => run copy fuel (copy s)

/-- Existing KMX value law is reached by induction over the local native
copy cut. This is a source/window association, not a new copy implementation. -/
theorem run_eq {Frame : Type} (copy : InitState Frame → InitState Frame)
    (cut : NCE_Native_CountCopy copy) (fuel : Nat) (s : InitState Frame)
    (small : s.n ≤ 16) (span : s.cursor+fuel ≤ s.n)
    (range : ∀ k, k < s.n → s.source k < 262144) :
    run copy fuel s = {s with memory := KMX_CopyMeaning.loop s.source s.memory s.cursor fuel, cursor:=s.cursor+fuel} := by
  induction fuel generalizing s with
  | zero => simp only [run,KMX_CopyMeaning.loop,Nat.add_zero]
  | succ fuel ih =>
    rw [run,copy_eq copy cut s (by omega) small range]
    let next : InitState Frame := {s with memory:=KMX_CopyMeaning.write s.memory s.cursor (s.source s.cursor),cursor:=s.cursor+1}
    have nextSpan : next.cursor+fuel ≤ next.n := by change s.cursor+1+fuel ≤ s.n; omega
    rw [ih next small nextSpan range]
    have cursor : s.cursor+1+fuel = s.cursor+(fuel+1) := by omega
    simp only [next,KMX_CopyMeaning.loop,cursor]

/-- Constructed native prefix initialization agrees with the EXISTING NBV
initial carrier, including its zero suffix and the SAME caller frame. -/
theorem initialized {Frame : Type}
    (create : (Nat → Nat) → Nat → Frame → InitState Frame)
    (zeroCut : NCE_Native_CountZero create) (copy : InitState Frame → InitState Frame)
    (copyCut : NCE_Native_CountCopy copy) (source : Nat → Nat) (n : Nat) (frame : Frame)
    (small : n ≤ 16) (range : ∀ k, k < n → source k < 262144) :
    run copy n (create source n frame) =
      ⟨source,NBV_CountInitialization.initialized source n,n,n,frame⟩ := by
  rw [create_eq create zeroCut source n frame small]
  rw [run_eq copy copyCut n _ small (by change 0+n ≤ n; omega) range]
  simp only [NBV_CountInitialization.initialized,Nat.zero_add] <;> rfl

#print axioms create_eq
#print axioms copy_eq
#print axioms run_eq
#print axioms initialized
end AspisR1.NCE_CountInitCuts
