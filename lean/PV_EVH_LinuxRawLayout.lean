import PV_EVH_EntropyDeployedLayout
import PV_EVH_LinuxRawABI
import PV_EVH_LinuxRawBounds
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawLayout
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawABI (inputs modulus)
open PV_EVH_LinuxRawHistory (Call execute)
open PV_EVH_EntropyDeployedLayout (field seed)
open PV_EVH_StackZero (State)

/-- The actual reservation extent discharges suffix_inputs' original64 bound;
there is no independent pointer-fit assumption for any syscall retry. -/
theorem suffix_inputs (sp offset : Nat) (hframe : sp+232 ≤ modulus)
    (ho : offset ≤ 64) :
    let r := inputs (sp+offset) (64-offset)
    r.rax = 318 ∧ r.rdi = sp+offset ∧ r.rsi = 64-offset ∧ r.rdx = 0 ∧
    r.rdi < modulus ∧ r.rsi < modulus :=
  PV_EVH_LinuxRawABI.suffix_inputs sp offset (by omega) ho

/-- Every request in the source-shaped driver fits physical registers and
precedes both inner slots and all three returned-Self staging regions. This is
request geometry on ALL outcome prefixes, not a kernel write-footprint proof. -/
theorem requests (syscall : Nat → Nat → Array U8 64#usize → PV_EVH_World.World →
      PV_EVH_LinuxRawControl.Reply)
    (owner sp fuel : Nat) (a : Array U8 64#usize) (w : State)
    (hframe : sp+232 ≤ modulus) (c : Call)
    (hc : c ∈ (execute syscall sp fuel 0 a w.frame.runtime.base).calls) :
    c.address < modulus ∧ c.length < modulus ∧ c.address+c.length = sp+64 ∧
    (∀ i, i < c.length →
      c.address+i < (field owner sp w).address ∧
      c.address+i < (seed owner sp w).address ∧ c.address+i < sp+128) := by
  have h := PV_EVH_LinuxRawBounds.requests syscall sp fuel 0 a w.frame.runtime.base
    (by omega) c hc
  unfold PV_EVH_LinuxRawBounds.Suffix at h
  change c.address < modulus ∧ c.length < modulus ∧ c.address+c.length = sp+64 ∧
    (∀ i, i < c.length → c.address+i < sp+64 ∧ c.address+i < sp+96 ∧ c.address+i < sp+128)
  unfold modulus at *
  omega

#print axioms suffix_inputs
#print axioms requests
end PV_EVH_LinuxRawLayout
