import RPu_FJj_TensorOuterCell
import RPu_FJj_TensorOuterBody
import RPu_FJj_TensorPrefix
import RPu_FJj_ArrayReadTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorOuterStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
abbrev Row := Array (Array NQ 4#usize) 5#usize
abbrev State := FIo_RangeNext.Range × FIo_Native.weights.Weights × Slice NQ × Usize

def Inv (self : FIo_Native.weights.Weights) (row : Row) (len : Nat) (t : State) : Prop :=
  t.1.end.val=5 ∧ 2≤t.1.start.val ∧ t.1.start.val≤5 ∧ t.2.1=self ∧
  FJj_QMSlice.canon t.2.2.1 ∧ t.2.2.1.val.length=len ∧
  t.2.2.2.val=4^(t.1.start.val-2) ∧ ∀ j,j<t.2.2.2.val →
    FJj_QMSlice.value t.2.2.1 j=FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) (t.1.start.val-2) j

def Post (row : Row) (len : Nat) (out : Slice NQ) : Prop :=
  FJj_QMSlice.canon out ∧ out.val.length=len ∧ ∀ j,j<64 →
    FJj_QMSlice.value out j=FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) 3 j

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (self : FIo_Native.weights.Weights) (k : Usize) (row : Row)
    (hr : Array.index_usize self.factors k=ok row)
    (hc : ∀ digit∈row.val,FJf_QMArray.canon digit) (len : Nat)
    (t : State) (inv : Inv self row len t) (out : ControlFlow State (Slice NQ))
    (run : FIo_Native.weights.Weights.tensor_loop0.body k t.1 t.2.1 t.2.2.1 t.2.2.2=ok out) :
    match out with
    | .done result => Post row len result
    | .cont next => Inv self row len next ∧ measure next < measure t := by
  rcases t with ⟨iter,current,input,n⟩
  rcases inv with ⟨he,lower,upper,es,cs,hl,wn,hv⟩
  change current=self at es
  change iter.end.val=5 at he
  change 2≤ iter.start.val at lower
  change iter.start.val≤5 at upper
  change FJj_QMSlice.canon input at cs
  change input.val.length=len at hl
  change n.val=4^(iter.start.val-2) at wn
  change ∀ j,j<n.val → FJj_QMSlice.value input j=
    FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) (iter.start.val-2) j at hv
  change FIo_Native.weights.Weights.tensor_loop0.body k iter current input n=ok out at run
  subst current
  cases out with
  | done result =>
    obtain ⟨stop,rfl⟩ := FJj_TensorOuterBody.done k n iter self input result run
    have last : iter.start.val=5 := by omega
    have nw : n.val=64 := by rw [last] at wn;exact wn
    exact ⟨cs,hl,by intro j hj;simpa only [last] using hv j (by omega)⟩
  | cont next =>
    rcases next with ⟨cursor,selfOut,output,nOut⟩
    obtain ⟨d,hnext⟩ := FJj_TensorOuterBody.cont k n nOut iter cursor self selfOut input output run
    have pr := FIo_RangeNext.some_next iter cursor d hnext
    have active : iter.start.val < 5 := by omega
    obtain ⟨digit,hd⟩ := FJj_ArrayReadTotal.value row d (by change d.val<5;rw [pr.1];exact active)
    have cd := hc digit (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hd))
    have small : n.val≤16 := by
      have choices : iter.start.val-2=0 ∨ iter.start.val-2=1 ∨ iter.start.val-2=2 := by omega
      rcases choices with h|h|h <;> rw [h] at wn <;> norm_num only at wn <;> omega
    have np : 0<n.val := by rw [wn];positivity
    obtain ⟨same,co,length,width,values⟩ := FJj_TensorOuterCell.value self selfOut k d n nOut row digit hr hd
      small np input output cd cs iter cursor hnext run
    dsimp only [Inv]
    refine ⟨⟨?_,?_,?_,same,co,length.trans hl,?_,?_⟩,?_⟩
    · rw [pr.2.1];exact he
    · omega
    · omega
    · have ds : cursor.start.val-2=(iter.start.val-2)+1 := by omega
      rw [ds,pow_succ,←wn,width,Nat.mul_comm]
    · intro j hj
      have ht : j<4*n.val := by omega
      rw [values j ht,hv (j%n.val) (Nat.mod_lt j np)]
      have ds : cursor.start.val-2=(iter.start.val-2)+1 := by omega
      rw [ds,FJj_TensorPrefix.prefixValue,←wn]
      have di : d.val=(iter.start.val-2)+2 := by rw [pr.1];omega
      rw [←di,FJj_TensorPrefix.read row d digit hd]
    · simp only [measure,pr.2.1,pr.2.2.1];have := pr.2.2.2;omega
#print axioms step
end AspisR1.FJj_TensorOuterStep
end
