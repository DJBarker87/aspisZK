import FJj_QMSliceUpdate
import FJa_ReverseStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorCell
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
open FJa_ReverseStep (Rev next)

def index (j n : Usize) (s : Usize) : Usize :=
  Usize.wrapping_add j (Usize.wrapping_mul s n)

theorem source (self : FIo_Native.weights.Weights) (k d n j : Usize)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize self.factors k=ok row) (hd : Array.index_usize row d=ok digit)
    (iter cursor : Rev) (input out : Slice NQ)
    (hn : next iter=ok (some j,cursor))
    (run : FIo_Native.weights.Weights.tensor_loop0_loop0.body self k n d iter input=
      ok (.cont (cursor,out))) :
    ∃ (x q0 q1 q2 q3 p0 p1 p2 p3 : NQ) (s0 s1 s2 : Slice NQ),
      Slice.index_usize input j=ok x ∧
      Array.index_usize digit 0#usize=ok q0 ∧
      FIo_Native.aspis_core.field.QM31.mul x q0=ok p0 ∧
      Slice.update input (index j n 0#usize) p0=ok s0 ∧
      Array.index_usize digit 1#usize=ok q1 ∧
      FIo_Native.aspis_core.field.QM31.mul x q1=ok p1 ∧
      Slice.update s0 (index j n 1#usize) p1=ok s1 ∧
      Array.index_usize digit 2#usize=ok q2 ∧
      FIo_Native.aspis_core.field.QM31.mul x q2=ok p2 ∧
      Slice.update s1 (index j n 2#usize) p2=ok s2 ∧
      Array.index_usize digit 3#usize=ok q3 ∧
      FIo_Native.aspis_core.field.QM31.mul x q3=ok p3 ∧
      Slice.update s2 (index j n 3#usize) p3=ok out := by
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body at run
  unfold next at hn
  rw [hn] at run
  simp only [bind_tc_ok] at run
  obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [hr,hd,bind_tc_ok] at run
  obtain ⟨q0,hq0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p0,hp0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨s0,hs0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p1,hp1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨s1,hs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p2,hp2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨s2,hs2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p3,hp3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨s3,hs3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨x,q0,q1,q2,q3,p0,p1,p2,p3,s0,s1,s2,hx,hq0,hp0,hs0,hq1,hp1,hs1,hq2,hp2,hs2,hq3,hp3,hs3⟩
#print axioms source
end AspisR1.FJj_TensorCell
end
