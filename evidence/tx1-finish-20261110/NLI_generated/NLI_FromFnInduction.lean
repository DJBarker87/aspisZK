import NLI_SourceEquality
import NLC_CopyFrames
set_option autoImplicit false
namespace AspisR1.NLI_FromFn
open Aeneas Aeneas.Std AspisR1PublicPreparation NLC_Finish
abbrev Memory := Nat → Option Q
def write (memory : Memory) (i : Nat) (value : Q) : Memory :=
 fun j=>if j=i then some value else memory j
def Initialized (values : Nat → Q) (count : Nat) (memory : Memory) : Prop :=
 ∀ j,j<count → memory j=some (values j)
theorem write_prefix (values : Nat → Q) (i : Nat) (memory : Memory)
 (before : Initialized values i memory) :
 Initialized values (i+1) (write memory i (values i)) := by
 intro j inside
 by_cases same:j=i
 · subst j; simp [write]
 · have hj : j < i := by omega
   simpa only [write,if_neg same] using before j hj
/-- The arbitrary native pre-cell can be initialized or uninitialized. No
property of the unwritten tail is required by this source invariant. -/
def fill (values : Nat → Q) : Nat → Nat → Memory → Memory
 | 0,_,memory=>memory
 | n+1,start,memory=>fill values n (start+1) (write memory start (values start))
theorem fill_prefix (values : Nat → Q) (count start : Nat) (memory : Memory)
 (before : Initialized values start memory) :
 Initialized values (start+count) (fill values count start memory) := by
 induction count generalizing start memory with
 | zero=>simpa only [fill,Nat.add_zero] using before
 | succ n ih=>
   have next:=write_prefix values start memory before
   have final:=ih (start+1) (write memory start (values start)) next
   simpa only [fill,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using final
/-- Disjointness for the actual16-byte QM31 write is the existing exact KMX
frame law, not a whole-buffer execution or a new copy stub. -/
theorem byte_frame {T : Type} (src dst : Nat → T) (base i outside : Nat)
 (separate : outside<base+16*i ∨ base+16*i+16≤outside) :
 KMX_CopyMeaning.loop src dst (base+16*i) 16 outside=dst outside :=
 NLC_CopyFrames.retained_window src dst (base+16*i) 16 outside separate
#print axioms write_prefix
#print axioms fill_prefix
#print axioms byte_frame
end AspisR1.NLI_FromFn
