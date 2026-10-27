import FJg_ScalarCell
import FIo_GroupCanonical
import FIp_RangeNone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ScalarFold
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
abbrev C := FJg_ScalarCell.C
abbrev State := FIo_RangeNext.Range × C × NE
abbrev iterator := core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize
abbrev operation := FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact

def body (t : State) := FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  iterator operation t.1 t.2.1 t.2.2

def Inv (p : Array NE 4#usize) (f : Array NQ 4#usize) (t : State) : Prop :=
  t.2.1=(p,f) ∧ t.1.end.val=4 ∧ t.1.start.val≤4 ∧ FIo_WideValues.Canon t.2.2 ∧
    decodeWide (wide t.2.2)=FJg_ScalarCell.sumPrefix p f t.1.start.val

def Post (p : Array NE 4#usize) (f : Array NQ 4#usize) (out : NE) : Prop :=
  FIo_WideValues.Canon out ∧ decodeWide (wide out)=FJg_ScalarCell.sumPrefix p f 4

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (p : Array NE 4#usize) (f : Array NQ 4#usize) (hp : FIo_ArrayCanon.Holds p)
    (t : State) (inv : Inv p f t) (out : ControlFlow State NE) (run : body t=ok out) :
    match out with
    | .done r => Post p f r
    | .cont next => Inv p f next ∧ measure next < measure t := by
  rcases t with ⟨iter,c,v⟩
  dsimp only [Inv] at inv
  rcases inv with ⟨rfl,he,hs,hv,value⟩
  unfold body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    have stop := FIp_RangeNone.none_next iter cursor hn
    have eq : iter.start.val=4 := by omega
    exact ⟨hv,by simpa only [eq] using value⟩
  | some s =>
    obtain ⟨⟨next,c'⟩,hcall,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have pr := FIo_RangeNext.some_next iter cursor s hn
    have sv := FJg_ScalarCell.value p f hp v next hv s c' hcall
    dsimp only [Inv]
    refine ⟨⟨sv.1,by rw [pr.2.1];exact he,by omega,sv.2.1,?_⟩,?_⟩
    · rw [sv.2.2,value,pr.2.2.1,FJg_ScalarCell.sumPrefix,pr.1]
    · simp only [measure,pr.2.1,pr.2.2.1];omega

theorem four (p : Array NE 4#usize) (f : Array NQ 4#usize) (hp : FIo_ArrayCanon.Holds p)
    (out : NE)
    (run : FIo_Native.core.iter.traits.iterator.Iterator.fold.default iterator operation
      {start:=0#usize,«end»:=4#usize} FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO (p,f)=ok out) :
    Post p f out := by
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default
    FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop at run
  exact FIo_LoopInvariant.preserve body (Inv p f) (Post p f) measure
    (fun t h r hr=>by cases r <;> exact step p f hp t h _ hr)
    ({start:=0#usize,«end»:=4#usize},(p,f),FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) out
    ⟨rfl,rfl,by change (0:Nat)≤4;decide,FIo_Constants.zero.1,by simpa only [show (0#usize).val=0 from by decide,FJg_ScalarCell.sumPrefix] using FIo_Constants.zero.2⟩ run
#print axioms step
#print axioms four
end AspisR1.FJg_ScalarFold
end
