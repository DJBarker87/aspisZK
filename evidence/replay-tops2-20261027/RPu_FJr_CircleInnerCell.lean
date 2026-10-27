import RPu_FJr_DoubleValue
import RPu_FJf_CircleBody
import RPu_FJf_FactorArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleInnerCell
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
open FJf_PointBody (Factors)
abbrev FK := OraclePortCheckpointAbiC5.K

def quad (x y : FK) (s : Fin 4) : FK :=
  match s.val with | 0=>1 | 1=>x | 2=>y | _=>x*y

theorem value (k : Usize) (iter cursor : FIo_RangeNext.Range)
    (factors next : Factors) (x x' : SQ) (cx : Canon x)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k iter factors x=
      ok (.cont (cursor,next,x'))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    Canon x' ∧ decode x'=FJd_LoopReference.double (FJd_LoopReference.double (decode x)) ∧
    ∃ (di : Usize) (row updated : FJf_FactorArray.Row) (back : FJf_FactorArray.Row → Factors)
      (digit : Array SQ 4#usize),
      di=iter.start ∧ Array.index_mut_usize factors (Usize.wrapping_add 3#usize k)=ok (row,back) ∧
      Array.update row di digit=ok updated ∧ next=back updated ∧
      FJc_WeightArray.canonical digit ∧ ∀ s : Fin 4,
        FJc_WeightArray.value digit s.val=quad (decode x) (FJd_LoopReference.double (decode x)) s := by
  unfold FIn_WeightsExtract.weights_new_loop1_loop0.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none=>cases run
  | some di=>
    obtain ⟨y,hy,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨idx,hidx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨row,back⟩,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨x1,hx1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have ei := Result.ok.inj hidx
    subst idx
    have pr := FIo_RangeNext.some_next iter cursor di hn
    have vy := FJr_DoubleValue.value x y cx hy
    have vq := FJc_WeightValues.mul x y q cx vy.1 hq
    have vx := FJr_DoubleValue.value y x' vy.1 hx1
    refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,vx.1,by rw [vx.2,vy.2],di,row,updated,back,_,pr.1,hr,hu,rfl,?_,?_⟩
    · intro v hv
      change v∈[FIn_WeightsExtract.field.QM31.ONE,x,y,q] at hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl|rfl
      · exact FJc_WeightConstants.one.1
      · exact cx
      · exact vy.1
      · exact vq.1
    · intro s
      fin_cases s
      · change decode FIn_WeightsExtract.field.QM31.ONE=1
        exact FJc_WeightConstants.one.2
      · rfl
      · change decode y=FJd_LoopReference.double (decode x)
        exact vy.2
      · change decode q=decode x*FJd_LoopReference.double (decode x)
        rw [vq.2,vy.2]

#print axioms value
end AspisR1.FJr_CircleInnerCell
end
