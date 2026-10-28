import R1Z.PV_RunJoin_FourChildren44
import R1Z.PV_RunJoin_FoldThread44
import R1Z.PV_RunJoin_WideUnique44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldStepValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

def model (q : Nat → Raw) (a : Raw) (dual : Bool) (i : Nat) : Exact :=
  if dual then PV_RunJoin_DualCell44.polynomial (fun s => q (4*i+s)) (value a)
  else PV_RunJoin_FoldCell44.polynomial (fun s => q (4*i+s)) (value a)

theorem cell (ops : ExternalFuns) (q : Nat → Raw) (a : Raw) (dual : Bool)
    (hc : ∀ s, s < 4 → canonical (q s)) (ha : canonical a) :
    ∃ z : Raw, @prover.fold_cell _ (ProverRwP6BodyCandidate.selected ops)
      (array 4#usize q) (current (source a)) dual = .ok (current (source z)) ∧
      canonical z ∧ value z = model q a dual 0 := by
  cases dual with
  | false => simpa only [model,Bool.false_eq_true,↓reduceIte,Nat.mul_zero,Nat.zero_add] using
      PV_RunJoin_FoldCell44.cell ops q hc a ha
  | true => simpa only [model,Bool.false_eq_true,↓reduceIte,Nat.mul_zero,Nat.zero_add] using
      PV_RunJoin_DualCell44.cell ops q hc a ha

theorem step (ops : ExternalFuns) (count : Usize) (q : Nat → Raw) (a : Raw) (dual : Bool)
    (hc : ∀ j, j < count.val → canonical (q j)) (ha : canonical a)
    (i : Usize) (hi : i.val < 256) (bound : 4*i.val + 4 ≤ count.val)
    (out : alloc.vec.Vec W) (room : out.length + 1 ≤ Usize.max) :
    ∃ (z : Raw) (next : alloc.vec.Vec W),
      @PV_RunJoin_FoldThread44.step _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (current (source a)) dual out i = .ok next ∧
      next.val = out.val ++ [current (source z)] ∧ canonical z ∧ value z = model q a dual i.val := by
  obtain ⟨z,hz,hcz,hdz⟩ := cell ops (fun s => q (4*i.val+s)) a dual
    (fun s hs => hc _ (by omega)) ha
  obtain ⟨next,hn,hnv⟩ := PV_RunJoin_Vector44.push out (current (source z)) room
  refine ⟨z,next,?_,hnv,hcz,?_⟩
  · unfold PV_RunJoin_FoldThread44.step
    rw [PV_RunJoin_FourChildren44.read_zero count q i hi bound,
      PV_RunJoin_FourChildren44.read count q i hi 1#usize (by decide) bound,
      PV_RunJoin_FourChildren44.read count q i hi 2#usize (by decide) bound,
      PV_RunJoin_FourChildren44.read count q i hi 3#usize (by decide) bound]
    simp only [bind_tc_ok,show (1#usize).val=1 from rfl,
      show (2#usize).val=2 from rfl,show (3#usize).val=3 from rfl]
    have four := PV_RunJoin_FourChildren44.four (fun s => current (source (q (4*i.val+s))))
    simp only [Nat.add_zero] at four
    rw [four]
    change (do
      let z ← @prover.fold_cell _ (ProverRwP6BodyCandidate.selected ops)
        (array 4#usize (fun s => q (4*i.val+s))) (current (source a)) dual
      alloc.vec.Vec.push out z) = _
    rw [hz]
    exact hn
  · simpa only [model,Nat.mul_zero,Nat.zero_add] using hdz
#print axioms cell
#print axioms step
end R1Z.PV_RunJoin_FoldStepValue44
