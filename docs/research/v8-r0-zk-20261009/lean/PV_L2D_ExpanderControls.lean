import PV_L2D_CollectedTrace
set_option autoImplicit false
namespace PV_L2D_ExpanderControls
open PV_L2D_ExpanderPort PV_L2D_ScalarPort PV_L2D_FourLimbs

def constant (w : UInt32) (_ : Seed) (_ : UInt64) : Cache := fun _=>w

theorem zero_accepts (s : State) (h : ∀ i, s.cache i=0) (n retry : Nat) :
    (sample (next (constant 0)) (n+1) retry s).value=some 0 ∧
    (sample (next (constant 0)) (n+1) retry s).consumed=1 := by
  have hw : (next (constant 0) s).word=0 := by
    simp only [next,constant]
    split <;> simp_all [constant]
  simp [sample,hw,PV_L2B_SourceWords.candidate]
#print axioms zero_accepts

theorem zero_after (s : State) (h : ∀ i, s.cache i=0) :
    ∀ i, (next (constant 0) s).after.cache i=0 := by
  intro i
  simp only [next,constant]
  split <;> simp_all [constant]
#print axioms zero_after

theorem zero_four (s : State) (h : ∀ i, s.cache i=0) :
    (collect (next (constant 0)) 16 4 s).value=some [0,0,0,0] ∧
    (collect (next (constant 0)) 16 4 s).consumed=4 := by
  have scalar : ∀ t : State, (∀ i,t.cache i=0) →
      (sample (next (constant 0)) 16 0 t).value=some 0 ∧
      (sample (next (constant 0)) 16 0 t).consumed=1 := fun t ht=>zero_accepts t ht 15 0
  have cache : ∀ t : State, (∀ i,t.cache i=0) →
      ∀ i,(sample (next (constant 0)) 16 0 t).after.cache i=0 := by
    intro t ht
    rw [after_exact,(scalar t ht).2]
    exact zero_after t ht
  have gen : ∀ k t, (∀ i,t.cache i=0) →
      (collect (next (constant 0)) 16 k t).value=some (List.replicate k 0) ∧
      (collect (next (constant 0)) 16 k t).consumed=k := by
    intro k
    induction k with
    | zero => intro t ht;simp [collect]
    | succ k ih =>
      intro t ht
      have a:=scalar t ht
      have b:=ih _ (cache t ht)
      simp [collect,a.1,a.2,b.1,b.2,List.replicate_succ,Nat.add_comm]
  simpa using gen 4 s h
#print axioms zero_four

/-- These are admitted cursor states with an actual successful and a rejected
word. The controls establish inhabitance, not deployed entropy support. -/
theorem initial_nonvacuity :
    (sample (next (constant 0)) 16 0 (initial (fun _=>0))).value=some 0 ∧
    (next (constant 2147483647) (initial (fun _=>0))).word=2147483647 := by
  constructor
  · exact (zero_accepts _ (fun _=>rfl) 15 0).1
  · simp [next,constant,initial]
#print axioms initial_nonvacuity
end PV_L2D_ExpanderControls
