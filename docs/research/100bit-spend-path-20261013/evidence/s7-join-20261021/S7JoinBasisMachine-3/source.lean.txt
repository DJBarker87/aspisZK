import S7JoinBasisBlock
import S7JoinBasisHighBit
import S7OwnedP6StoredNode
set_option autoImplicit false
namespace AspisR1.S7JoinBasisMachine
open Aeneas Aeneas.Std Result
open AspisCircleGroupOrder AspisCircleTensorBinding
open S7Kani2BasisLoop (Basis)
open S7Kani3BasisOuter (levels t2)
open S7JoinBasisBlock (cell)

def decode (x : U32) : ZMod P := x.val

theorem word_mul (x y : U32) :
    decode (S7Kani2PrefixLoop.wordMul x y)=decode x*decode y := by
  change (((x.val*y.val)%P : Nat) : ZMod P)=(x.val : ZMod P)*(y.val : ZMod P)
  rw [ZMod.natCast_mod,Nat.cast_mul]

theorem t2_exact (x : U32) : ∃ y,
    t2 x=ok y ∧ decode y=2*(decode x)^2-1 := by
  obtain ⟨m,hm,vm,cm⟩ := ExtractedCurrentReducer.current_mul_mod x x
  obtain ⟨d,hd,vd,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod m m cm cm
  obtain ⟨y,hy,vy,cy⟩ := ExtractedCurrentM31AddSub.current_sub_mod d 1#u32 cd (by decide)
  refine ⟨y,by simp only [t2,S7Kani3BasisOuter.double,hm,hd,hy,bind_tc_ok],?_⟩
  change (y.val : ZMod P)=_
  have vy1 : y.val=(d.val+P-1)%P := vy
  rw [vy1,ZMod.natCast_mod,Nat.cast_sub (by change 1≤d.val+2147483647; omega),Nat.cast_add,Nat.cast_one]
  have hp : (P : ZMod P)=0 := ZMod.natCast_self P
  rw [hp,add_zero,vd,ZMod.natCast_mod,Nat.cast_add,vm,ZMod.natCast_mod,Nat.cast_mul]
  change (x.val : ZMod P)*(x.val : ZMod P)+(x.val : ZMod P)*(x.val : ZMod P)-1=_
  simp only [decode]
  ring

/-- Meaning of the initialized prefix, without assumptions about unused cells. -/
def Prefix (b : Basis) (x : ZMod P) (width : Nat) : Prop :=
  ∀ j, j<width → decode (cell b j)=naturalLineValue x j

theorem block_prefix (b : Basis) (node : U32) (x : ZMod P) (depth : Nat)
    (n : Usize) (hn : n.val=2^depth) (bound : n.val≤128)
    (hb : Prefix b x n.val) (hnode : decode node=doubledFactor x depth) :
    ∃ out, S7Kani2BasisLoop.basis_block_owned
      AspisR1Qm31ArithmeticProbe.field.M31.mul b node n 0#usize=ok out ∧
      Prefix out x (2*n.val) := by
  obtain ⟨out,ho,hcells⟩ := S7JoinBasisBlock.block_exact b node n 0#usize n.val bound (by simp)
  refine ⟨out,ho,?_⟩
  intro j hj
  rw [hcells j (by omega)]
  by_cases low : j<n.val
  · rw [if_neg (by change ¬(n.val+0≤j ∧ j<2*n.val); omega)]
    exact hb j low
  · rw [if_pos (by change n.val+0≤j ∧ j<2*n.val; omega),word_mul,hb (j-n.val) (by omega),hnode]
    have he : j=2^depth+(j-n.val) := by omega
    conv_rhs => rw [he,S7JoinBasisHighBit.natural_high _ _ _ (by omega)]

theorem levels_prefix (fuel depth : Nat) (x : ZMod P) (b : Basis) (node : U32) (n : Usize)
    (hn : n.val=2^depth) (bound : n.val*2^fuel≤256)
    (hb : Prefix b x n.val) (hnode : decode node=doubledFactor x depth) :
    ∃ out, levels fuel b node n=ok out ∧ Prefix out x (n.val*2^fuel) := by
  induction fuel generalizing depth b node n with
  | zero => exact ⟨b,rfl,by simpa using hb⟩
  | succ fuel ih =>
      have hp : 0<2^fuel := by positivity
      have hle : n.val≤n.val*2^fuel := Nat.le_mul_of_pos_right _ hp
      have hs : n.val*2^fuel*2≤256 := by simpa [pow_succ,Nat.mul_assoc] using bound
      obtain ⟨b1,hb1,hpre⟩ := block_prefix b node x depth n hn (by omega) hb hnode
      obtain ⟨node1,hnode1,hdec⟩ := t2_exact node
      obtain ⟨n1,hmul,hn1⟩ := ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (n.val*2) (by scalar_tac)
      have htimes : (n*2#usize : Result Usize)=ok n1 := hmul
      have hpow : n1.val=2^(depth+1) := by rw [hn1,hn,pow_succ]
      have hnodeNext : decode node1=doubledFactor x (depth+1) := by
        rw [hdec,hnode,doubledFactor]
      obtain ⟨out,ho,hout⟩ := ih (depth+1) b1 node1 n1 hpow
        (by rw [hn1]; simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs)
        (by simpa only [hn1,Nat.mul_comm] using hpre) hnodeNext
      refine ⟨out,by simp only [levels,hb1,hnode1,htimes,bind_tc_ok]; exact ho,?_⟩
      simpa only [hn1,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hout

#print axioms word_mul
#print axioms t2_exact
#print axioms block_prefix
#print axioms levels_prefix
end AspisR1.S7JoinBasisMachine
