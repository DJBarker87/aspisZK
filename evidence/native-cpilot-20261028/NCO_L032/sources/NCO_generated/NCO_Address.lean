import NCO_WordStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Address

theorem geometry (n i j : Nat) (cap : n ≤ 3712) (row : i < n/32) (lane : j < 8) :
    i < 116 ∧ 32*i + 4*j + 3 < n ∧ 32*i + 4*j + 3 < 3712 := by omega

structure Arithmetic (i j : Usize) where
  p q at1 a1 a2 a3 next : Usize
  mul0 : 32#usize * i = ok p
  mul1 : 4#usize * j = ok q
  add : p + q = ok at1
  add1 : at1 + 1#usize = ok a1
  add2 : at1 + 2#usize = ok a2
  add3 : at1 + 3#usize = ok a3
  increment : j + 1#usize = ok next
  at_val : at1.val = 32*i.val + 4*j.val
  a1_val : a1.val = at1.val + 1
  a2_val : a2.val = at1.val + 2
  a3_val : a3.val = at1.val + 3
  next_val : next.val = j.val + 1

theorem arithmetic (i j : Usize) (hi : i.val < 116) (hj : j.val < 8) :
    Nonempty (Arithmetic i j) := by
  have sm0 : (32#usize * i : Result Usize) ⦃ x => x.val = 32*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨p,hp,vp⟩ := WP.spec_imp_exists sm0
  have sm1 : (4#usize * j : Result Usize) ⦃ x => x.val = 4*j.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨q,hq,vq⟩ := WP.spec_imp_exists sm1
  have sa : (p + q : Result Usize) ⦃ x => x.val = p.val + q.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨at1,ha,va⟩ := WP.spec_imp_exists sa
  have s1 : (at1 + 1#usize : Result Usize) ⦃ x => x.val = at1.val+1 ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨a1,h1,v1⟩ := WP.spec_imp_exists s1
  have s2 : (at1 + 2#usize : Result Usize) ⦃ x => x.val = at1.val+2 ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨a2,h2,v2⟩ := WP.spec_imp_exists s2
  have s3 : (at1 + 3#usize : Result Usize) ⦃ x => x.val = at1.val+3 ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨a3,h3,v3⟩ := WP.spec_imp_exists s3
  have sn : (j + 1#usize : Result Usize) ⦃ x => x.val = j.val+1 ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨next,hn,vn⟩ := WP.spec_imp_exists sn
  exact ⟨{p:=p,q:=q,at1:=at1,a1:=a1,a2:=a2,a3:=a3,next:=next,
    mul0:=hp,mul1:=hq,add:=ha,add1:=h1,add2:=h2,add3:=h3,increment:=hn,
    at_val:=by omega,a1_val:=v1,a2_val:=v2,a3_val:=v3,next_val:=vn}⟩

def byte (payload : Slice U8) (n : Nat) : U8 := payload.val[n]?.getD 0#u8

theorem read (payload : Slice U8) (i : Usize) (h : i.val < payload.val.length) :
    Slice.index_usize payload i = ok (byte payload i.val) := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec payload i (by simpa only [Slice.length] using h))
  rw [value] at run
  simpa only [byte,List.getElem?_eq_getElem h,Option.getD_some] using run

#print axioms geometry
#print axioms arithmetic
#print axioms read
end NCO_Address
