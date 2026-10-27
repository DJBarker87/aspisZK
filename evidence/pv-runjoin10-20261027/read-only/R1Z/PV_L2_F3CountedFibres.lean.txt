import R1Z.ProverCommitSequentialArrays

/-! Successful decoder fibres conditioned on EVERY scalar's rejection count.
This is stronger than unconditioned equal fibres: refill/cursor/partial-word
control is retained, without enumerating any Word stream. Failed runs are
not discarded from the experiment; this lemma is only its success fibre. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3CountedFibres
open R1Z.ProverCommitSequentialFibres
attribute [local instance] Classical.propDecidable

variable {W A : Type} [Fintype W]

def tagged (d : W → Option A) (r : Nat) (w : W) : Option (A × Nat) :=
  (d w).map (fun a => (a,17-r))

def counted (d : W → Option A) : (n L r : Nat) → (Fin n → W) → Option (Values (A × Nat) L)
  | 0,0,_,_ => some PUnit.unit
  | 0,_+1,_,_ => none
  | _+1,0,_,_ => some PUnit.unit
  | _+1,_+1,0,_ => none
  | n+1,L+1,r+1,ws =>
      step (tagged d (r+1)) (counted d n (L+1) r) (counted d n L 16)
        (ws 0, fun j => ws j.succ)

def counts : (L : Nat) → Values (A × Nat) L → Values Nat L
  | 0,_ => PUnit.unit
  | L+1,out => (out.1.2,counts L out.2)

theorem tagged_card (d : W → Option A) (c : Nat)
    (fibres : ∀ a, (Finset.univ.filter (fun w => d w = some a)).card = c)
    (r : Nat) (out : A × Nat) :
    (Finset.univ.filter (fun w => tagged d r w = some out)).card =
      if out.2 = 17-r then c else 0 := by
  rcases out with ⟨a,count⟩
  by_cases he : count = 17-r
  · rw [if_pos he]
    have hh : (Finset.univ.filter (fun w => tagged d r w = some (a,count))) =
        Finset.univ.filter (fun w => d w = some a) := by
      ext w
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      cases hd : d w <;> simp [tagged,hd,he]
    rw [hh,fibres]
  · rw [if_neg he]
    have hh : (Finset.univ.filter (fun w => tagged d r w = some (a,count))) = ∅ := by
      ext w
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
      cases hd : d w <;> simp [tagged,hd,Ne.symm he]
    rw [hh,Finset.card_empty]

theorem card_rec (d : W → Option A) (n L r : Nat) (out : Values (A × Nat) (L+1)) :
    (Finset.univ.filter (fun ws : Fin (n+1) → W => counted d (n+1) (L+1) (r+1) ws = some out)).card =
    (Finset.univ.filter (fun w => tagged d (r+1) w = none)).card *
      (Finset.univ.filter (fun ws : Fin n → W => counted d n (L+1) r ws = some out)).card +
    (Finset.univ.filter (fun w => tagged d (r+1) w = some out.1)).card *
      (Finset.univ.filter (fun ws : Fin n → W => counted d n L 16 ws = some out.2)).card := by
  let eqv : {ws : Fin (n+1) → W // counted d (n+1) (L+1) (r+1) ws = some out} ≃
      {bt : W × (Fin n → W) // step (tagged d (r+1))
        (counted d n (L+1) r) (counted d n L 16) bt = some out} := {
    toFun := fun ws => ⟨wordTailEquiv W n ws.1,ws.2⟩
    invFun := fun bt => ⟨(wordTailEquiv W n).symm bt.1,bt.2⟩
    left_inv := fun ws => Subtype.ext ((wordTailEquiv W n).left_inv ws.1)
    right_inv := fun bt => Subtype.ext ((wordTailEquiv W n).right_inv bt.1) }
  have hc := Fintype.card_congr eqv
  simp only [Fintype.card_subtype] at hc
  have hs := step_fibre_card (tagged d (r+1))
    (counted d n (L+1) r) (counted d n L 16) out
  calc
    _ = (Finset.univ.filter (fun bt : W × (Fin n → W) => step (tagged d (r+1))
      (counted d n (L+1) r) (counted d n L 16) bt = some out)).card := by
        convert hc using 1 <;> congr 1 <;> ext z <;>
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      convert hs using 4 <;> congr 1 <;> ext z <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]

/-- For any two successful scalar arrays with the SAME full draw counts,
the source-input fibres have the same size. No common cF is assumed. -/
theorem conditional_equal_fibres (d : W → Option A) (c : Nat)
    (fibres : ∀ a, (Finset.univ.filter (fun w => d w = some a)).card = c)
    (n L r : Nat) (out out' : Values (A × Nat) L) (same : counts L out = counts L out') :
    (Finset.univ.filter (fun ws : Fin n → W => counted d n L r ws = some out)).card =
      (Finset.univ.filter (fun ws : Fin n → W => counted d n L r ws = some out')).card := by
  induction n generalizing L r with
  | zero =>
    cases L with
    | zero => cases out;cases out';rfl
    | succ L => simp only [counted,reduceCtorEq,Finset.filter_false]
  | succ n ih =>
    cases L with
    | zero => cases out;cases out';rfl
    | succ L =>
      cases r with
      | zero => simp only [counted,reduceCtorEq,Finset.filter_false]
      | succ r =>
        have hh : out.1.2 = out'.1.2 := congrArg Prod.fst same
        have ht : counts L out.2 = counts L out'.2 := congrArg Prod.snd same
        rw [card_rec,card_rec]
        rw [ih (L+1) r out out' same, ih L 16 out.2 out'.2 ht,
          tagged_card d c fibres, tagged_card d c fibres,hh]

#print axioms tagged_card
#print axioms card_rec
#print axioms conditional_equal_fibres
end R1Z.PV_L2_F3CountedFibres
