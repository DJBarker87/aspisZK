import AspisR1ProducerRelease47.Opening48
import R1Z.ProverCommitWideBytes48
import R1Z.ProverCommitBasisCounter47
/-! Complete 29-lane source-owner coefficient mix on full WideExact values.
The native one-iteration gate is trace-parametric; gamma-power and source
coefficient provenance are separate callers, not hypotheses of the loop law. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMix48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48

def sourceArray (size : Usize) (xs : Nat → Raw) : Array Source size :=
  ⟨List.ofFn (fun i : Fin size.val => source (xs i.val)),by simp⟩

theorem index (size : Usize) (xs : Nat → Raw) (i : Usize) (hi : i.val<size.val) :
    Array.index_usize (sourceArray size xs) i=ok (source (xs i.val)) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ hi]
  simp only [sourceArray,List.getElem_ofFn]

def sum (q p : Nat → Raw) : Nat → Nat → Exact
 | 0,_ => 0
 | n+1,i => value (p i)*value (q i)+sum q p n (i+1)

def finite : Nat → Array Source 29#usize → Array Source 29#usize → Usize → Source → Result Source
 | 0,_,_,_,s => ok s
 | n+1,q,p,i,s => do
  let p1 ← Array.index_usize p i
  let q1 ← Array.index_usize q i
  let product ← field.wide_exact.WideExact.mul p1 q1
  let next ← field.wide_exact.WideExact.add s product
  finite n q p (Usize.wrapping_add i 1#usize) next

theorem source_finite (n : Nat) (left : U8) (hleft : left.val=n)
    (q p : Array Source 29#usize) (i : Usize) (s : Source) :
    mix q p i left s=finite n q p i s := by
  induction n generalizing left i s with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [mix,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have ht : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)]
      omega
    rw [mix]
    simp only [hn,if_false,finite,lift,bind_tc_ok]
    have tail : ∀ v, mix q p (Usize.wrapping_add i 1#usize)
        (U8.wrapping_sub left 1#u8) v=finite n q p (Usize.wrapping_add i 1#usize) v :=
      fun v => ih _ ht _ v
    simp only [tail]

attribute [local irreducible] sourceArray value source sum

theorem finite_value (q p : Nat → Raw)
    (hq : ∀ j, j<29 → canonical (q j)) (hp : ∀ j, j<29 → canonical (p j))
    (n : Nat) (i : Usize) (bound : i.val+n≤29) (s : Raw) (hs : canonical s) :
    ∃ z : Raw, finite n (sourceArray 29#usize q) (sourceArray 29#usize p) i (source s)=ok (source z) ∧
      canonical z ∧ value z=value s+sum q p n i.val := by
  induction n generalizing i s with
  | zero => exact ⟨s,rfl,hs,by rw [sum,add_zero]⟩
  | succ n ih =>
    have hi : i.val<29 := by omega
    have hin : i.val<(29#usize).val := hi
    have hiq := index 29#usize q i hin
    have hip := index 29#usize p i hin
    obtain ⟨product,hprod,hcprod,hdprod⟩ := mul_exact (p i.val) (q i.val) (hp _ hi) (hq _ hi)
    obtain ⟨next,hnext,hcnext,hdnext⟩ := add_exact s product hs hcprod
    have hinc : (Usize.wrapping_add i 1#usize).val=i.val+1 :=
      ProverCommitPairCounter47.next_val i (by omega)
    have hbound : (Usize.wrapping_add i 1#usize).val+n≤29 := by rw [hinc];omega
    obtain ⟨z,hz,hcz,hdz⟩ := ih _ hbound next hcnext
    refine ⟨z,?_,hcz,?_⟩
    · simp only [finite,hip,hiq,hprod,hnext,bind_tc_ok,hz]
    · rw [hdz,hdnext,hdprod,hinc,sum]
      ring

theorem owner_value (q p : Nat → Raw)
    (hq : ∀ j, j<29 → canonical (q j)) (hp : ∀ j, j<29 → canonical (p j))
    (s : Raw) (hs : canonical s) :
    ∃ z : Raw, mix (sourceArray 29#usize q) (sourceArray 29#usize p) 0#usize 29#u8 (source s)=ok (source z) ∧
      canonical z ∧ value z=value s+sum q p 29 0 := by
  rw [source_finite 29 _ rfl]
  exact finite_value q p hq hp 29 0#usize (by scalar_tac) s hs

#print axioms index
#print axioms source_finite
#print axioms finite_value
#print axioms owner_value
end R1Z.ProverCommitMix48
