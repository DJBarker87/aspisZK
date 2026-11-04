import PV_EVH_KernelMemory
import PV_EVH_LinuxRawBounds
import PV_EVH_LinuxRawThreaded
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RawMemoryHistory
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_KernelMemory (Memory Backed Step)
open PV_EVH_LinuxRawHistory (Call execute)
open PV_EVH_World (World)

abbrev MemoryAnswer := Nat → Nat → Array U8 64#usize → World → Memory → Memory

/-- Replay only physical syscall memory transitions, on the existing private
source history. No public event or helper result is reconstructed from memory. -/
def replay (memory : MemoryAnswer) : List Call → Memory → Memory
  | [], m => m
  | c::cs, m => replay memory cs (memory c.address c.length c.before c.worldBefore m)

/-- Each private receipt contains the actual selected raw answer at that
point of the advancing source history, including terminal failure prefixes. -/
theorem answers
    (syscall : Nat → Nat → Array U8 64#usize → World → PV_EVH_LinuxRawControl.Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World) :
    ∀ c ∈ (execute syscall address fuel offset a w).calls,
      c.after = syscall c.address c.length c.before c.worldBefore := by
  induction fuel generalizing offset a w with
  | zero => simp only [execute,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ fuel ih =>
    intro c hc
    simp only [execute,List.mem_cons] at hc
    rcases hc with hc | hc
    · subst c; rfl
    · cases hr : (syscall (address+offset) (64-offset) a w).result with
      | fault e => simp only [hr,List.not_mem_nil] at hc
      | exhausted => simp only [hr,List.not_mem_nil] at hc
      | returned r =>
        cases r with
        | fail e => simp only [hr,List.not_mem_nil] at hc
        | div => simp only [hr,List.not_mem_nil] at hc
        | ok ret =>
          simp only [hr] at hc
          split_ifs at hc <;> first | exact ih _ _ _ c hc | simp only [List.not_mem_nil] at hc

/-- A continuously backed physical run: neither the consumed prefix nor
external memory is discarded when a source call errors or the fuel ends. -/
theorem threaded (memory : MemoryAnswer) (address : Nat)
    (calls : List Call) (a b : Array U8 64#usize) (w v : World) (m : Memory)
    (ht : PV_EVH_LinuxRawThreaded.Threaded a w calls b v)
    (hv : ∀ c ∈ calls, ∀ before, Backed address c.before before →
      Step address (c.address-address) before
        (memory c.address c.length c.before c.worldBefore before) c.after.buffer)
    (hb : Backed address a m) :
    Backed address b (replay memory calls m) ∧
    ∀ p, p < address ∨ address+64 ≤ p → replay memory calls m p = m p := by
  induction calls generalizing a w m with
  | nil =>
    obtain ⟨rfl,rfl⟩ := ht
    exact ⟨hb,fun _ _ => rfl⟩
  | cons c cs ih =>
    obtain ⟨hc,hw,htail⟩ := ht
    have hs := hv c List.mem_cons_self m (hc ▸ hb)
    have htail := ih c.after.buffer c.after.world _ htail
      (fun d hd => hv d (List.mem_cons_of_mem c hd)) hs.1
    refine ⟨htail.1,?_⟩
    intro p hp
    exact (htail.2 p hp).trans (hs.2 p (by omega))

#print axioms answers
#print axioms threaded
end PV_EVH_RawMemoryHistory
