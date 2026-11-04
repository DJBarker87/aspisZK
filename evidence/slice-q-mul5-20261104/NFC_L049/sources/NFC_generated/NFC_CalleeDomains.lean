import NFC_DotPushTotal
import NEV_DotCarrier
set_option autoImplicit false
noncomputable section
namespace NFC_CalleeDomains
open Aeneas Aeneas.Std Result AspisR1 NEV_DotCarrier
-- Generic LPi_CheckedInputs / NBQ_QChecks / LPi_PublicPush proof structure,
-- with their exact coordinate predicates isolated from unused S1 fixtures.
def q (x : NQ) : FIo_Native.fast_pairing.canonical.Q :=
 Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
theorem private_canon (x : NQ) (canonical : canonQ x) : NFC_RawValues.Canon (q x) := by
 rcases canonical with ⟨⟨a,b⟩,⟨c,d⟩⟩
 simp only [NFC_RawValues.Canon,q,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ]
 exact ⟨by omega,by omega,by omega,by omega⟩

theorem from_wide (v : NE) : FIo_Native.fast_pairing.canonical.Q.from_wide v=
 ok (Array.make 2#usize [q v.c0,q v.c1]) := rfl

theorem from_limbs (a b c d : U32) :
 FIo_Native.fast_pairing.canonical.Q.from_limbs (Array.make 4#usize [a,b,c,d])=
 ok (if a<2147483647#u32 ∧ b<2147483647#u32 ∧ c<2147483647#u32 ∧ d<2147483647#u32
   then some (Array.make 4#usize [a,b,c,d]) else none) := by
 simp only [FIo_Native.fast_pairing.canonical.Q.from_limbs,
   FIo_Native.fast_pairing.canonical.P,Array.index_usize,Array.make]
 split_ifs <;> simp_all

theorem checked (x : NQ) (canonical : canonQ x) :
 FIo_Native.fast_pairing.checked_q x=ok (.Ok (q x)) := by
 rcases canonical with ⟨⟨a,b⟩,⟨c,d⟩⟩
 have valid : x.c0.a<2147483647#u32 ∧ x.c0.b<2147483647#u32 ∧
   x.c1.a<2147483647#u32 ∧ x.c1.b<2147483647#u32 :=
   ⟨by scalar_tac,by scalar_tac,by scalar_tac,by scalar_tac⟩
 have check:=from_limbs x.c0.a x.c0.b x.c1.a x.c1.b
 rw [if_pos valid] at check
 simp only [FIo_Native.fast_pairing.checked_q,FIo_Native.fast_pairing.limbs_of,check,bind_tc_ok]
 rfl

theorem value (v : NE) (canonical : canonE v) :
 FIo_Native.fast_pairing.canonical.Q.from_wide v=ok (Array.make 2#usize [q v.c0,q v.c1]) ∧
 NFC_RawValues.Canon (q v.c0) ∧ NFC_RawValues.Canon (q v.c1) :=
 ⟨from_wide v,private_canon v.c0 canonical.1,private_canon v.c1 canonical.2⟩
/-- SAME accepted check derives its private operand domain. -/
theorem scalar (x : NQ) (actual : FIo_Native.fast_pairing.canonical.Q)
 (run : FIo_Native.fast_pairing.checked_q x=ok (.Ok actual)) :
 canonQ x ∧ actual=q x ∧ NFC_RawValues.Canon actual := by
 change FIo_Native.fast_pairing.checked_q x=ok (.Ok actual) at run
 by_cases valid : x.c0.a<2147483647#u32 ∧ x.c0.b<2147483647#u32 ∧
     x.c1.a<2147483647#u32 ∧ x.c1.b<2147483647#u32
 · have canonical : canonQ x := ⟨⟨by scalar_tac,by scalar_tac⟩,⟨by scalar_tac,by scalar_tac⟩⟩
   have same : actual=q x := by
     have h:=(checked x canonical).symm.trans run
     cases h
     rfl
   exact ⟨canonical,same,by rw [same];exact private_canon x canonical⟩
 · have check:=from_limbs x.c0.a x.c0.b x.c1.a x.c1.b
   rw [if_neg valid] at check
   simp only [FIo_Native.fast_pairing.checked_q,FIo_Native.fast_pairing.limbs_of,check,bind_tc_ok] at run
   cases run
/-- Whole actual successful push and counter are derived from input domains. -/
theorem total (self : FIo_Native.fast_pairing.EbyKDot) (v : NE) (x : NQ)
 (hv : canonE v) (hx : canonQ x) (count : self.count.val<4096) :
 ∃ out,FIo_Native.fast_pairing.EbyKDot.push self v x=ok (.Ok (),out) ∧
   out.count.val=self.count.val+1 := by
 have ca:=private_canon v.c0 hv.1
 have cb:=private_canon v.c1 hv.2
 have cq:=private_canon x hx
 obtain ⟨a,ha⟩:=NFC_DotPushTotal.source self.c0 _ _ ca cq
 obtain ⟨b,hb⟩:=NFC_DotPushTotal.source self.c1 _ _ cb cq
 have below : ¬self.count≥FIo_Native.fast_pairing.MAX_TERMS := by
   simp only [FIo_Native.fast_pairing.MAX_TERMS];scalar_tac
 have i0 : Array.index_usize (Array.make 2#usize [q v.c0,q v.c1]) 0#usize=ok (q v.c0) := rfl
 have i1 : Array.index_usize (Array.make 2#usize [q v.c0,q v.c1]) 1#usize=ok (q v.c1) := rfl
 refine ⟨⟨a,b,Usize.wrapping_add self.count 1#usize⟩,?_,?_⟩
 · simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg below,from_wide,bind_tc_ok,
     checked x hx,core.result.Result.Insts.CoreOpsTry.branch,i0,i1,ha,hb,lift]
 · rw [Usize.wrapping_add_val_eq]
   apply Nat.mod_eq_of_lt
   have limit:=(4096#usize).hSize
   change 4096<UScalar.size .Usize at limit
   change self.count.val+1<UScalar.size .Usize
   omega
#print axioms private_canon
#print axioms from_wide
#print axioms from_limbs
#print axioms checked
#print axioms value
#print axioms scalar
#print axioms total
end NFC_CalleeDomains
end
