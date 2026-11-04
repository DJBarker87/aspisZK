import PV_EVH_EntropyDeployedLayout
set_option autoImplicit false
namespace PV_EVH_PhysicalFrame
/-! D585: binary-structural (adopted da36d6aa), plus V370 compiler-cohort.
This is the concrete stack interpretation, NOT an allocator interpretation or
an assertion that every supplied source State is a reached machine state. -/
inductive SlotId where
  | inner (index : Fin 6)
  | mask (retry : Fin 8)
  | result (retry : Fin 8)
  deriving DecidableEq

/-- Result records its 97 initialized bytes, not Rust allocation padding. -/
def offset : SlotId → Nat
  | .inner i => if i.val = 0 then 0 else 32 + 32*i.val
  | .mask i => 304 + 336*i.val
  | .result i => 352 + 336*i.val

def extent : SlotId → Nat
  | .inner i => if i.val = 0 then 64 else 32
  | .mask _ => 32
  | .result _ => 97

structure Lifetime where
  activation : Nat
  iteration : Nat
  deriving DecidableEq

structure Slot where
  address : Nat
  bytes : Nat
  lifetime : Lifetime

/-- Local addresses are reused across iterations; their lifetimes are not. -/
def table (sp activation iteration : Nat) : SlotId → Slot
  | id@(.inner _) => ⟨sp + offset id, extent id, ⟨activation,iteration⟩⟩
  | id@(.mask i) => ⟨sp + offset id, extent id, ⟨activation+1+i.val,0⟩⟩
  | id@(.result i) => ⟨sp + offset id, extent id, ⟨activation+1+i.val,0⟩⟩

def Separate (a b : Slot) : Prop :=
  a.address+a.bytes ≤ b.address ∨ b.address+b.bytes ≤ a.address

/-- Geometry is proved, never included as a field of the interface. -/
theorem offsets_separate (a b : SlotId) (hne : a ≠ b) :
    offset a + extent a ≤ offset b ∨ offset b + extent b ≤ offset a := by
  cases a with
  | inner i =>
    cases b with
    | inner j =>
      have hij : i.val ≠ j.val := by
        intro h; exact hne (congrArg SlotId.inner (Fin.ext h))
      simp only [offset,extent]
      split_ifs <;> omega
    | mask j => simp only [offset,extent]; split_ifs <;> omega
    | result j => simp only [offset,extent]; split_ifs <;> omega
  | mask i =>
    cases b with
    | inner j => simp only [offset,extent]; split_ifs <;> omega
    | mask j =>
      have hij : i.val ≠ j.val := by
        intro h; exact hne (congrArg SlotId.mask (Fin.ext h))
      simp only [offset,extent]; omega
    | result j => simp only [offset,extent]; omega
  | result i =>
    cases b with
    | inner j => simp only [offset,extent]; split_ifs <;> omega
    | mask j => simp only [offset,extent]; omega
    | result j =>
      have hij : i.val ≠ j.val := by
        intro h; exact hne (congrArg SlotId.result (Fin.ext h))
      simp only [offset,extent]; omega

theorem table_separate (sp activation iteration : Nat) (a b : SlotId) (h : a ≠ b) :
    Separate (table sp activation iteration a) (table sp activation iteration b) := by
  have hg := offsets_separate a b h
  cases a <;> cases b <;> simp only [table,Separate] <;> omega

inductive Phase where
  | beforeInit | original | halves | staging | returned | stopped
  deriving DecidableEq

/-- Liveness is source-lifetime/phase sensitive. Staging and moved-from bytes
remain present in memory even when this predicate is false. -/
def live (phase : Phase) (retry : Fin 8) (id : SlotId) : Prop :=
  match id with
  | .inner i =>
    match phase with
    | .beforeInit | .returned | .stopped => False
    | .original => i.val = 0
    | .halves => i.val < 3
    | .staging => True
  | .mask i => i.val ≤ retry.val
  | .result i => i.val < retry.val ∨ (i = retry ∧ phase = .returned)

structure Activation where
  identity : Nat
  sp : Nat
  reservation : Nat
  deriving DecidableEq

/-- Oldest first; current retry has index zero in the physical slot table. -/
def retryChain (sp activation : Nat) : Nat → List Activation
  | 0 => []
  | n+1 => ⟨activation+1+n,sp+288+336*n,264⟩ :: retryChain sp activation n

theorem chain_length (sp activation n : Nat) :
    (retryChain sp activation n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [retryChain,List.length_cons,ih]

structure Request where
  thread : Nat
  activation : Nat
  sp : Nat
  bytes : Nat
  stackLimit : Nat

/-- Residence is a post-answer resource fact, including demand growth.
The answer does not promise future accesses or identify any heap owner. -/
structure Grant (request : Request) where
  lower : Nat
  upper : Nat
  writable : Nat → Prop
  contains : lower ≤ request.sp ∧ request.sp+request.bytes ≤ upper
  nonwrap : upper ≤ 2^64
  rw : ∀ p, lower ≤ p → p < upper → writable p

inductive StackAnswer (request : Request) where
  | pending
  | granted (grant : Grant request)
  | exhausted (fault : PV_EVH_Runtime.Fault)

/-- Real data fields. Shape is supplied by interpret, not assumed consistency. -/
structure Frame where
  sp : Nat
  activation : Nat
  retry : Fin 8
  iteration : Fin 16
  phase : Phase
  slotTable : SlotId → Slot
  offsets : SlotId → Nat
  lifetimes : SlotId → Lifetime
  activeFrames : List Activation
  request : Request
  answer : StackAnswer request

/-- No heap, register or memory is synthesized by this constructor. -/
def interpret (thread activation sp stackLimit : Nat) (retry : Fin 8)
    (iteration : Fin 16) (phase : Phase)
    (answer : StackAnswer ⟨thread,activation,sp,232,stackLimit⟩) : Frame :=
  ⟨sp,activation,retry,iteration,phase,table sp activation iteration.val,offset,
   fun id => (table sp activation iteration.val id).lifetime,
   retryChain sp activation (retry.val+1),
   ⟨thread,activation,sp,232,stackLimit⟩,answer⟩

theorem live_nonoverlap (thread activation sp stackLimit : Nat) (retry : Fin 8)
    (iteration : Fin 16) (phase : Phase)
    (answer : StackAnswer ⟨thread,activation,sp,232,stackLimit⟩)
    (a b : SlotId) (_ha : live phase retry a) (_hb : live phase retry b) (hne : a ≠ b) :
    Separate ((interpret thread activation sp stackLimit retry iteration phase answer).slotTable a)
      ((interpret thread activation sp stackLimit retry iteration phase answer).slotTable b) :=
  table_separate sp activation iteration.val a b hne

theorem public_depth (thread activation sp stackLimit : Nat) (retry : Fin 8)
    (iteration : Fin 16) (phase : Phase)
    (answer : StackAnswer ⟨thread,activation,sp,232,stackLimit⟩) :
    (interpret thread activation sp stackLimit retry iteration phase answer).activeFrames.length ≤ 8 := by
  change (retryChain sp activation (retry.val+1)).length ≤ 8
  rw [chain_length]
  omega

theorem granted_bytes (request : Request) (g : Grant request) (i : Nat)
    (hi : i < request.bytes) :
    request.sp+i < 2^64 ∧ g.writable (request.sp+i) := by
  have hc := g.contains
  have hn := g.nonwrap
  constructor
  · omega
  · apply g.rw <;> omega

#print axioms offsets_separate
#print axioms table_separate
#print axioms chain_length
#print axioms live_nonoverlap
#print axioms public_depth
#print axioms granted_bytes
end PV_EVH_PhysicalFrame
