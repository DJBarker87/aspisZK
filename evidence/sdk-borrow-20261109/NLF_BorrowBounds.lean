import NLF_ProgramFold
import NLF_CounterLaws
import NLF_RuntimeInterpretation
set_option autoImplicit false
namespace NLF_BorrowBounds
open NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_ProgramFold

def Bounded (s : State) : Prop := ∀ i, -1≤flag (s.cells i) ∧ flag (s.cells i)≤9223372036854775807

theorem put_bound (s : State) (i : Nat) (c : Cell Payload) (h : Bounded s)
    (hc : -1≤flag c ∧ flag c≤9223372036854775807) : Bounded (put s i c) := by
  intro j
  by_cases eq : j=i
  · simpa [put,eq] using hc
  · simpa [put,eq] using h j

theorem acquire_bound (p : Parent) (a : Nat) (k : Kind) (h : Bounded p.state) :
    Bounded (NLF_ParentModel.acquire p a k).1.state := by
  let i := (p.state.accounts a).data
  cases k with
  | shared =>
    by_cases ok : (p.state.cells i).writer=none ∧
      (p.state.cells i).readers.length<9223372036854775807 ∧ p.next∉(p.state.cells i).readers
    · change Bounded (wrap p.state i p.next .shared).1
      rw [shared_result p.state i p.next ok.1 ok.2.2 ok.2.1]
      apply put_bound _ _ _ h
      simp only [flag,ok.1,Int.ofNat_eq_natCast,List.length_cons]
      have hi := ok.2.1
      omega
    · simpa [NLF_ParentModel.acquire,wrap,shared,i,ok] using h
  | exclusive =>
    by_cases ok : (p.state.cells i).writer=none ∧ (p.state.cells i).readers=[]
    · change Bounded (wrap p.state i p.next .exclusive).1
      rw [exclusive_result p.state i p.next ok.1 ok.2]
      apply put_bound _ _ _ h
      simp [flag]
    · simpa [NLF_ParentModel.acquire,wrap,exclusive,i,ok] using h

theorem release_bound (p : Parent) (g : Guard) (v : Invariant p) (h : Bounded p.state) :
    Bounded (NLF_ParentModel.release p g).1.state := by
  cases hk : g.kind with
  | shared =>
    by_cases ok : (p.state.cells g.cell).writer=none ∧ g.token∈(p.state.cells g.cell).readers
    · have eq : NLF_SdkModel.release p.state g = .ok (put p.state g.cell
        {p.state.cells g.cell with readers:=(p.state.cells g.cell).readers.erase g.token}) := by
        simp [NLF_SdkModel.release,hk,dropShared,ok.1,ok.2]
      simp only [NLF_ParentModel.release,eq]
      apply put_bound _ _ _ h
      rw [NLF_CounterLaws.shared_current_counter _ _ ok]
      have positive := NLF_CounterLaws.shared_positive _ _ ok
      have old := h g.cell
      omega
    · simpa [NLF_ParentModel.release,NLF_SdkModel.release,hk,dropShared,ok] using h
  | exclusive =>
    by_cases ok : (p.state.cells g.cell).writer=some g.token
    · have eq : NLF_SdkModel.release p.state g = .ok (put p.state g.cell {p.state.cells g.cell with writer:=none}) := by
        simp [NLF_SdkModel.release,hk,dropExclusive,ok]
      simp only [NLF_ParentModel.release,eq]
      apply put_bound _ _ _ h
      rw [NLF_CounterLaws.exclusive_zero _ _ (v.1 g.cell) ok]
      omega
    · simpa [NLF_ParentModel.release,NLF_SdkModel.release,hk,dropExclusive,ok] using h

theorem step_bound (p : Parent) (c : Command) (v : Invariant p) (h : Bounded p.state) :
    Bounded (NLF_ProgramFold.step p c).state := by
  cases c with
  | acquire a k => exact acquire_bound p a k h
  | deref g => simpa [NLF_ProgramFold.step,NLF_ParentModel.deref] using h
  | release g => exact release_bound p g v h
  | write g value =>
    intro i
    simpa only [NLF_ProgramFold.step,NLF_ViewLaws.write_counter] using h i

theorem fold_bound (p : Parent) (cs : List Command) (v : Invariant p) (h : Bounded p.state) :
    Bounded (NLF_ProgramFold.run p cs).state := by
  induction cs generalizing p with
  | nil => exact h
  | cons c cs ih => exact ih (NLF_ProgramFold.step p c) (step_invariant p c v) (step_bound p c v h)

theorem admitted_bound {F : Type} (h : AspisR1.S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (cs : List Command) :
    Bounded (NLF_ProgramFold.run (NLF_RuntimeInterpretation.install h records money) cs).state := by
  apply fold_bound _ _ (NLF_RuntimeInterpretation.install_invariant h records money)
  intro i
  simp [NLF_RuntimeInterpretation.install,NLF_Admission.initial,flag]

#print axioms put_bound
#print axioms acquire_bound
#print axioms release_bound
#print axioms step_bound
#print axioms fold_bound
#print axioms admitted_bound
end NLF_BorrowBounds
