import NBA_QueryTrace
set_option autoImplicit false
namespace AspisR1.NBA_QueryConstruct
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitScanBody Query31ExplicitListLoop Query31ExplicitScanConcreteSteps
open NBA_QueryTrace

theorem construct (words : List U32) (s : State) (valid : validState s) :
    ∃ final stop, Trace words s final stop ∧ validState final := by
  induction words generalizing s with
  | nil => exact ⟨s,some false,.exhausted s,valid⟩
  | cons x xs ih =>
    by_cases full : s.accepted_len=22#usize ∨ s.draws=64#usize
    · exact ⟨s,none,.stopped x xs s full,valid⟩
    · have hlen : s.accepted_len.val<22 := by
        have b := valid.1
        have n : s.accepted_len≠22#usize := fun h => full (Or.inl h)
        scalar_tac
      have hdraw : s.draws.val<64 := by
        have b := valid.2.1
        have n : s.draws≠64#usize := fun h => full (Or.inr h)
        scalar_tac
      by_cases mem : x.val ∈ acceptedPrefix s
      · have small : s.draws.val+(1#usize).val≤UScalar.max .Usize := by scalar_tac
        obtain ⟨d,hd,vd⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=s.draws) (y:=1#usize) small)
        let next : State := {s with draws:=d}
        have frame : NBA_QueryStep.Frame s next x true := by
          refine ⟨?_,?_,rfl⟩
          · simpa only [next] using vd
          · simp only [next,↓reduceIte,Nat.add_zero]
        have validNext := NBA_QueryStep.valid hlen hdraw frame
        obtain ⟨final,stop,tail,good⟩ := ih next validNext
        exact ⟨final,stop,.continuing x xs s next final stop hlen hdraw true (by simp only [mem,decide_true]) frame tail,good⟩
      · obtain ⟨d,n,a,hd,vd,hn,vn,ha,hbody,rest⟩ :=
          fresh_from_bounds listNext (x::xs) xs s x rfl hlen hdraw mem
        have aeq : a=s.accepted.set s.accepted_len x := Result.ok.inj (ha.symm.trans (NBA_QueryStep.update s x hlen))
        let next : State := {accepted:=a,accepted_len:=n,draws:=d}
        have frame : NBA_QueryStep.Frame s next x false := by
          refine ⟨vd,?_,?_⟩
          · simpa only [next,Bool.false_eq_true,↓reduceIte] using vn
          · simp only [next,Bool.false_eq_true,↓reduceIte,aeq]
            rfl
        have validNext := NBA_QueryStep.valid hlen hdraw frame
        obtain ⟨final,stop,tail,good⟩ := ih next validNext
        exact ⟨final,stop,.continuing x xs s next final stop hlen hdraw false (by simp only [mem,decide_false]) frame tail,good⟩

#print axioms construct
end AspisR1.NBA_QueryConstruct
