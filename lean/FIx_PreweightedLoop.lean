import FIx_PreweightedLoopStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIx_PreweightedLoopStep (loop)
abbrev R := core.ops.range.RangeInclusive Usize

def remaining (r : R) : Nat :=
  if r.exhausted=true ∨ r.end.val<r.start.val then 0 else r.end.val-r.start.val+1

def model {N : Usize} (a : Array NQ N) (start : Nat) : Nat → Nat → (Fin (24#usize).val → K) → (Fin (24#usize).val → K)
  | 0,_,old => old
  | n+1,group,old => model a start n (group+1) (FIx_PreweightedGroup.step a start group old)

theorem value {N : Usize} (r : R) (packed out : Array NQ 24#usize)
    (start : Usize) (a : Array NQ N) (hend : r.end.val<24)
    (hp : canonical packed) (ha : canonical a)
    (success : loop r packed start a=ok out) :
    canonical out ∧ decoded out=model a start.val (remaining r) r.start.val (decoded packed) := by
  generalize hcount : remaining r=count
  induction count using Nat.strong_induction_on generalizing r packed with
  | h count ih =>
    obtain ⟨pair,hnext,hpost⟩ := WP.spec_imp_exists
      (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
    rcases pair with ⟨o,r'⟩
    by_cases hempty : r.exhausted=true ∨ r.end.val<r.start.val
    · simp only [if_pos hempty] at hpost
      rcases hpost with ⟨rfl,rfl⟩
      have zero : count=0 := by simpa only [remaining,if_pos hempty] using hcount.symm
      rw [FIx_PreweightedLoopStep.value,hnext,bind_tc_ok] at success
      have same : packed=out := Result.ok.inj success
      subst out
      exact ⟨hp,by rw [zero];rfl⟩
    · have hs : r.start.val≤r.end.val := by omega
      by_cases hlt : r.start.val<r.end.val
      · simp only [if_neg hempty,if_pos hlt] at hpost
        rcases hpost with ⟨rfl,hstep,hend',hexhausted⟩
        rw [FIx_PreweightedLoopStep.value,hnext,bind_tc_ok] at success
        change (do let next←FIx_PreweightedGroup.run packed r.start start a; loop r' next start a)=ok out at success
        obtain ⟨next,hgroup,tail⟩ := FIv_Map.bind_success _ _ _ success
        have vg := FIx_PreweightedGroup.value packed next r.start start a (by simpa using (show r.start.val<24 by omega)) hp ha hgroup
        have hremaining : remaining r'+1=count := by
          rw [←hcount]
          unfold remaining
          simp only [if_neg hempty,hexhausted,Bool.false_eq_true,false_or,hend']
          rw [if_neg (by omega)]
          omega
        have rest := ih (remaining r') (by omega) r' next (by simpa only [hend'] using hend) vg.1 tail rfl
        refine ⟨rest.1,?_⟩
        rw [rest.2,←hremaining,model,vg.2,hstep]
      · simp only [if_neg hempty,if_neg hlt] at hpost
        rcases hpost with ⟨rfl,hsame,hend',hexhausted⟩
        rw [FIx_PreweightedLoopStep.value,hnext,bind_tc_ok] at success
        change (do let next←FIx_PreweightedGroup.run packed r.start start a; loop r' next start a)=ok out at success
        obtain ⟨next,hgroup,tail⟩ := FIv_Map.bind_success _ _ _ success
        have vg := FIx_PreweightedGroup.value packed next r.start start a (by simpa using (show r.start.val<24 by omega)) hp ha hgroup
        have hremaining : remaining r'=0 := by simp only [remaining,hexhausted,true_or,↓reduceIte]
        have hone : count=1 := by rw [←hcount];unfold remaining;rw [if_neg hempty];omega
        have rest := ih 0 (by omega) r' next (by simpa only [hend'] using hend) vg.1 tail hremaining
        exact ⟨rest.1,by simpa only [hone,model] using rest.2.trans vg.2⟩
#print axioms value
end AspisR1.FIx_PreweightedLoop
end
