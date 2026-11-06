import NJB_PreparedLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowPowers
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- Native power window K098/K099 multiplies AFTER saving each current
power, including the eighth multiplication whose returned value is unused. -/
def run (lambda : NQ) : Nat → NQ → Result (List NQ × NQ)
 | 0,power=>ok ([],power)
 | n+1,power=>do
  let next ← FIq_Native.field.QM31.mul power lambda
  let rest ← run lambda n next
  ok (power::rest.1,rest.2)
inductive Trace (lambda : NQ) : Nat → NQ → List NQ → NQ → Prop
 | nil (p : NQ) : Trace lambda 0 p [] p
 | cons {n p middle values last} (multiply : FIq_Native.field.QM31.mul p lambda=ok middle)
   (tail : Trace lambda n middle values last) : Trace lambda (n+1) p (p::values) last
/-- Symbolic power recurrence, no evaluation of a concrete field numeral. -/
theorem source (lambda power : NQ) (n : Nat) (hl : Canon lambda) (hp : Canon power) :
 ∃ values next,run lambda n power=ok (values,next) ∧ Trace lambda n power values next ∧
 values.length=n ∧ (∀ x∈values,Canon x) ∧ Canon next ∧
 (∀ i (hi : i<values.length),decode values[i]=decode power*decode lambda^i) ∧
 decode next=decode power*decode lambda^n := by
 induction n generalizing power with
 | zero =>
  refine ⟨[],power,rfl,.nil power,rfl,by simp,hp,?_,?_⟩
  · intro i hi;simp at hi
  · simp
 | succ n ih =>
  obtain ⟨middle,cm,hm,vm⟩ := NJB_StubLaws.qm_mul power lambda hp hl
  obtain ⟨values,next,cr,tr,length,canon,hn,words,last⟩ := ih middle hm
  refine ⟨power::values,next,?_,.cons cm tr,by simp [length],?_,hn,?_,?_⟩
  · simp only [run,cm,cr,bind_tc_ok]
  · intro x hx;rcases List.mem_cons.mp hx with rfl|h
    · exact hp
    · exact canon x h
  · intro i hi
    cases i with
    | zero => simp
    | succ i =>
     have bound : i<values.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
     simp only [List.getElem_cons_succ,words i bound,vm,pow_succ]
     ring
  · rw [last,vm,pow_succ];ring
#print source
#print axioms source
end AspisR1.NJL_WindowPowers
end
