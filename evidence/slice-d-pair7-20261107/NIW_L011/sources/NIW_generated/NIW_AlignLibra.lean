import NIT_LibraChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibra
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_LibraChain NIT_FieldInterpretation

def Reached (logs : Nat → Result LibraLog) (j : Nat) : Prop :=
 ∀ k,k<j → ∃ l,logs k=ok l

def run (cells : Nat → Parts) (logs : Nat → Result LibraLog) : Nat → Nat → Result Parts
 | 0,j=>ok (cells j)
 | n+1,j=>match logs j with | fail e=>fail e | div=>div | ok _=>run cells logs n (j+1)

/-- Only entered observations are required. An aborting field observation has
no subsequent multiplication/addition log, nor any suffix requirement. -/
def Association (f : Ref (Slice U8)) (libra : Powers) (cells : Nat → Parts)
 (logs : Nat → Result LibraLog) : Prop :=
 ∀ j,j<4 → Reached logs j →
 match logs j with
 | fail e=>FIo_Native.weights.field f.value (UScalar.ofNatCore j (by omega))=fail e
 | div=>FIo_Native.weights.field f.value (UScalar.ofNatCore j (by omega))=div
 | ok l=>cutLibraLog f libra j (cells j) l (cells (j+1)) ∧
   FIo_Native.weights.field f.value (UScalar.ofNatCore j (by omega))=ok l.coefficient ∧
   EMul l.mul_a l.mul_b l.product ∧ EAdd l.add_a l.add_b l.reply

theorem from_stream (f : Ref (Slice U8)) (libra : Powers)
 (cells : Nat → Parts) (logs : Nat → Result LibraLog) (association : Association f libra cells logs)
 (fuel : Nat) (range : NHI_RangeProgress.Range)
 (last : range.end.val=4) (bound : range.start.val≤4) (enough : 4-range.start.val<fuel)
 (reached : Reached logs range.start.val) :
 Trace f libra fuel (range,cells range.start.val) (run cells logs (4-range.start.val) range.start.val) := by
 induction fuel generalizing range with
 | zero=>omega
 | succ fuel ih=>
  by_cases active : range.start.val<4
  · have delta : 4-range.start.val=(4-(range.start.val+1))+1 := by omega
    have localLaw := association range.start.val active reached
    have index : UScalar.ofNatCore range.start.val (by omega)=range.start := by
     apply UScalar.eq_of_val_eq; rfl
    cases observed : logs range.start.val with
    | fail e=>
     simp only [observed,index] at localLaw
     have trace := Trace.failed f libra fuel (range,cells range.start.val) e last active localLaw
     simpa only [delta,run,observed] using trace
    | div=>
     simp only [observed,index] at localLaw
     have trace := Trace.diverged f libra fuel (range,cells range.start.val) last active localLaw
     simpa only [delta,run,observed] using trace
    | ok l=>
     simp only [observed,index] at localLaw
     obtain ⟨cut,field,mulLaw,addLaw⟩ := localLaw
     obtain ⟨rest,_,next,he,inc,_⟩ := NIT_LibraInterpretation.step f libra
      (range,cells range.start.val) (cells (range.start.val+1)) l cut field mulLaw addLaw last
     change rest.start.val=range.start.val+1 at inc
     have nextReached : Reached logs rest.start.val := by
      intro k hk
      rw [inc] at hk
      by_cases prior : k<range.start.val
      · exact reached k prior
      · have same : k=range.start.val := by omega
        subst k;exact ⟨l,observed⟩
     have tail := ih rest he (by omega) (by omega) nextReached
     rw [inc] at tail
     have trace := Trace.step f libra fuel (range,cells range.start.val)
      (run cells logs (4-(range.start.val+1)) (range.start.val+1)) (cells (range.start.val+1))
      l last cut field mulLaw addLaw rest next tail
     simpa only [delta,run,observed] using trace
  · have atEnd : range.start.val=4 := by omega
    have trace := Trace.done f libra fuel (range,cells range.start.val)
     (by change range.end.val≤range.start.val;omega)
    simpa only [atEnd,Nat.sub_self,run] using trace

#print axioms from_stream
end AspisR1.NIW_AlignLibra
