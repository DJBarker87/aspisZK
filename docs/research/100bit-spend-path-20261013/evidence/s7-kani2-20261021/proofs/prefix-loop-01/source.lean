import S7Kani2AccumulatorLoop
import ExtractedCurrentReducer

/- Literal emitted prefix loop with the actual already-proved frozen M31
multiply. Bounds cover the entire 110-entry geometry allocation. -/
set_option autoImplicit false
namespace S7Kani2PrefixLoop
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer

def prefixes_owned
  (flat : alloc.vec.Vec U32)
  (prefixes : alloc.vec.Vec U32)
  (product : U32) (index : Std.Usize) :
  Result ((alloc.vec.Vec U32) × (alloc.vec.Vec
    U32) × U32)
  := do
  let i := alloc.vec.Vec.len flat
  if index >= i
  then ok (flat, prefixes, product)
  else
    let prefixes1 ← alloc.vec.Vec.push prefixes product
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat index
    let product1 ← AspisR1Qm31ArithmeticProbe.field.M31.mul product m
    let i1 ← index + 1#usize
    prefixes_owned flat prefixes1 product1 i1
partial_fixpoint

def wordMul (x y : U32) : U32 :=
  UScalar.ofNatCore ((x.val*y.val)%P) (by
    have hm := Nat.mod_lt (x.val*y.val) (show 0<P by decide)
    have hp : P<2^32 := by decide
    omega)

theorem multiply_word (x y : U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y=ok (wordMul x y) := by
  obtain ⟨z,hz,hvalue,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
  have he : z=wordMul x y := UScalar.eq_of_val_eq hvalue
  simpa only [he] using hz

def model : List U32 → List U32 → U32 → List U32 × U32
 | [],prefixes,product => (prefixes,product)
 | x::xs,prefixes,product => model xs (prefixes++[product]) (wordMul product x)

/-- Complete total refinement of the actual emitted prefix loop. No
multiplication, push or step-equality hypothesis is assumed. -/
theorem prefixes_refines (flat : alloc.vec.Vec U32) (prefixes : alloc.vec.Vec U32)
    (product : U32) (index : Usize) (fuel : Nat)
    (hflat : flat.val.length≤110) (remaining : index.val+fuel=flat.val.length)
    (capacity : prefixes.val.length+fuel≤110) :
    ∃ prefixesOut productOut,
      prefixes_owned flat prefixes product index=ok (flat,prefixesOut,productOut) ∧
      (prefixesOut.val,productOut)=model (flat.val.drop index.val) prefixes.val product := by
  induction fuel generalizing index prefixes product with
  | zero =>
      have hstop : index ≥ alloc.vec.Vec.len flat := by scalar_tac
      refine ⟨prefixes,product,?_,?_⟩
      · rw [prefixes_owned]
        simp only [hstop,if_pos]
      · have hd : flat.val.drop index.val=[] := List.drop_eq_nil_iff.mpr (by omega)
        simp only [hd,model]
  | succ fuel ih =>
      have hb : index.val<flat.val.length := by omega
      have running : ¬ index ≥ alloc.vec.Vec.len flat := by scalar_tac
      have hcap : prefixes.val.length<Usize.max := by
        have hm : 110<Usize.max := by scalar_tac
        omega
      obtain ⟨prefixes1,hpush,hprefixes1⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec prefixes product hcap)
      obtain ⟨x,hread,hx⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec flat index hb)
      have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
          flat index=ok x := hread
      obtain ⟨index1,hinc,hindex1⟩ := S7Kani2AccumulatorLoop.increment index (by omega)
      have hc1 : prefixes1.val.length+fuel≤110 := by
        rw [hprefixes1,List.length_append]
        simp only [List.length_singleton]
        omega
      obtain ⟨out,finalProduct,hrun,hvalue⟩ := ih prefixes1 (wordMul product x) index1
        (by omega) hc1
      refine ⟨out,finalProduct,?_,?_⟩
      · rw [prefixes_owned]
        simp only [running,if_false,hpush,hr,multiply_word,hinc,bind_tc_ok]
        exact hrun
      · have hd : flat.val.drop index.val = x::flat.val.drop (index.val+1) := by
          simpa only [←hx] using (List.drop_eq_getElem_cons (l:=flat.val) hb)
        rw [hd,model]
        simpa only [hindex1,hprefixes1] using hvalue

#print axioms multiply_word
#print axioms prefixes_refines
end S7Kani2PrefixLoop
