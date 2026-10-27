import R1Z.PV_Src_ExternalMat4Copy
import R1Z.PV_Src_ExternalBlocks

/-! One source block, reduced symbolically through the exact matrix equation.
No concrete permutation or recurrence is normalized. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalBlockStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference
abbrev State := Array U32 16#usize

def base (g : Usize) : Usize := Usize.wrapping_mul g 4#usize

def write (s : State) (g : Usize) (m : Array U32 4#usize) : State :=
  (((s.set (base g) m.val[0]!).set (Usize.wrapping_add (base g) 1#usize) m.val[1]!).set
    (Usize.wrapping_add (base g) 2#usize) m.val[2]!).set
    (Usize.wrapping_add (base g) 3#usize) m.val[3]!

theorem base_val (g : Usize) (hg : g.val < 4) : (base g).val = 4*g.val := by
  unfold base
  rw [umul _ _ (by simp;omega)]
  simp only [UScalar.ofNatCore_val_eq]
  omega

theorem offset_val (g : Usize) (hg : g.val < 4) (k : Usize) (hk : k.val < 4) :
    (Usize.wrapping_add (base g) k).val = 4*g.val+k.val := by
  rw [uadd _ _ (by rw [base_val g hg];omega),base_val g hg]

theorem source (s : State) (g : Usize) (hg : g.val < 4)
    (m : Array U32 4#usize)
    (hm : R0PoseidonCopy.mat4 s.val[(base g).val]!
      s.val[(Usize.wrapping_add (base g) 1#usize).val]!
      s.val[(Usize.wrapping_add (base g) 2#usize).val]!
      s.val[(Usize.wrapping_add (base g) 3#usize).val]! = ok m) :
    poseidon2.builder_reference.external_owned_loop0 s g =
      poseidon2.builder_reference.external_owned_loop0 (write s g m)
        (Usize.wrapping_add g 1#usize) := by
  have b0 : (base g).val < (16#usize : Usize).val := by rw [base_val g hg];simp;omega
  have b1 : (Usize.wrapping_add (base g) 1#usize).val < (16#usize : Usize).val := by
    rw [offset_val g hg _ (by decide)];simp;omega
  have b2 : (Usize.wrapping_add (base g) 2#usize).val < (16#usize : Usize).val := by
    rw [offset_val g hg _ (by decide)];simp;omega
  have b3 : (Usize.wrapping_add (base g) 3#usize).val < (16#usize : Usize).val := by
    rw [offset_val g hg _ (by decide)];simp;omega
  rw [poseidon2.builder_reference.external_owned_loop0,if_pos (by simpa [UScalar.lt_equiv] using hg)]
  simp only [lift,bind_tc_ok]
  change (do
    let a ← Array.index_usize s (base g)
    let b ← Array.index_usize s (Usize.wrapping_add (base g) 1#usize)
    let c ← Array.index_usize s (Usize.wrapping_add (base g) 2#usize)
    let d ← Array.index_usize s (Usize.wrapping_add (base g) 3#usize)
    let x ← poseidon2.builder_reference.mat4_owned (Array.make 4#usize [a,b,c,d])
    let x0 ← Array.index_usize x 0#usize
    let s0 ← Array.update s (base g) x0
    let x1 ← Array.index_usize x 1#usize
    let s1 ← Array.update s0 (Usize.wrapping_add (base g) 1#usize) x1
    let x2 ← Array.index_usize x 2#usize
    let s2 ← Array.update s1 (Usize.wrapping_add (base g) 2#usize) x2
    let x3 ← Array.index_usize x 3#usize
    let s3 ← Array.update s2 (Usize.wrapping_add (base g) 3#usize) x3
    poseidon2.builder_reference.external_owned_loop0 s3 (Usize.wrapping_add g 1#usize)) = _
  simp only [index_ok s _ b0,index_ok s _ b1,index_ok s _ b2,index_ok s _ b3,bind_tc_ok,
    PV_Src_ExternalMat4Copy.equals_copy,Array.make]
  simp only [R0Z.PoseidonRefine.gl0,R0Z.PoseidonRefine.gl1,
    R0Z.PoseidonRefine.gl2,R0Z.PoseidonRefine.gl3]
  rw [hm]
  simp only [bind_tc_ok,index_ok m 0#usize (by decide),index_ok m 1#usize (by decide),
    index_ok m 2#usize (by decide),index_ok m 3#usize (by decide),
    update_ok _ _ _ b0,update_ok _ _ _ b1,update_ok _ _ _ b2,update_ok _ _ _ b3,write,UScalar.ofNatCore_val_eq]

#print axioms base_val
#print axioms offset_val
#print axioms source
end R1Z.PV_Src_ExternalBlockStep
