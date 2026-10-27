import RPv_FJg_PartialsCell
import RPu_FIo_GroupCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_PartialsValue
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ NE)
abbrev State := FIo_RangeNext.Range × Array NE 4#usize
abbrev R := core.result.Result (Array NE 4#usize) FIo_Native.verifier.Error

def Values (f : Slice U8) (common : Array NQ 16#usize) (p : Array NE 4#usize) (n : Nat) : Prop :=
  ∀ s : Usize,s.val < n → FIp_ArrayValue.value p s.val=FJf_PartialCell.sumPrefix f common s 16

def Inv (f : Slice U8) (common : Array NQ 16#usize) (t : State) : Prop :=
  t.1.end.val=4 ∧ t.1.start.val≤4 ∧ FIo_ArrayCanon.Holds t.2 ∧ Values f common t.2 t.1.start.val

def Post (f : Slice U8) (common : Array NQ 16#usize) : R → Prop
  | .Err _ => True
  | .Ok p => FIo_ArrayCanon.Holds p ∧ Values f common p 4

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (f : Slice U8) (common : Array NQ 16#usize) (hc : FJf_QMArray.canon common)
    (t : State) (inv : Inv f common t) (out : ControlFlow State R)
    (run : FIo_Native.weights.shared_partials_loop.body f common t.1 t.2=ok out) :
    match out with
    | .done r => Post f common r
    | .cont next => Inv f common next ∧ measure next < measure t := by
  rcases t with ⟨iter,p⟩
  dsimp only [Inv] at inv
  rcases inv with ⟨he,hs,hp,hv⟩
  cases out with
  | done r =>
    cases r with
    | Err e => trivial
    | Ok result =>
      unfold FIo_Native.weights.shared_partials_loop.body at run
      obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases o with
      | none =>
        cases Result.ok.inj run
        have stop := FIp_RangeNone.none_next iter cursor hn
        have eq : iter.start.val=4 := by omega
        exact ⟨hp,by simpa only [eq] using hv⟩
      | some s =>
        obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases r with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame,bind_tc_ok] at run
          cases run
        | Ok x =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
          obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
          cases run
  | cont next =>
    rcases next with ⟨cursor,next⟩
    obtain ⟨he',hs',more,cn,values⟩ := FJg_PartialsCell.value f common hc iter cursor p next he hp run
    dsimp only [Inv]
    refine ⟨⟨by rw [he'];exact he,by omega,cn,?_⟩,?_⟩
    · intro s h
      rw [values]
      by_cases eq : iter.start.val=s.val
      · rw [if_pos eq]
      · rw [if_neg eq]
        exact hv s (by omega)
    · simp only [measure,he',hs'];omega

theorem four (f : Slice U8) (common : Array NQ 16#usize) (hc : FJf_QMArray.canon common)
    (out : Array NE 4#usize) (run : FIo_Native.weights.shared_partials f common=ok (.Ok out)) :
    FIo_ArrayCanon.Holds out ∧ Values f common out 4 := by
  unfold FIo_Native.weights.shared_partials FIo_Native.weights.shared_partials_loop at run
  exact FIo_LoopInvariant.preserve
    (fun t : State=>FIo_Native.weights.shared_partials_loop.body f common t.1 t.2)
    (Inv f common) (Post f common) measure
    (fun t h r hr=>by cases r <;> exact step f common hc t h _ hr)
    ({start:=0#usize,«end»:=4#usize},Array.repeat 4#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)
    (.Ok out) ⟨rfl,by change (0:Nat)≤4;decide,FIo_GroupCanonical.zeros _,by intro s h;change s.val<0 at h;omega⟩ run
#print axioms step
#print axioms four
end AspisR1.FJg_PartialsValue
end
