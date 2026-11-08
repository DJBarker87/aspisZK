import NNU_MerkleRoot
set_option autoImplicit false
namespace AspisR1.NNU_MerkleWrapper
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem returned {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
 (root : Array U8 32#usize) (s out : reference.Scratch) (physical : Slice U8)
 (positive : 0 < s.n.val) (bound : s.n.val≤16)
 (indices : reference.valid_indices s.idx s.n 0#usize=.ok true)
 (aligned : physical.val.length%32=0)
 (run : reference.levels D hash {s with «at»:=0#usize} physical 18#u32=.ok (.Done out))
 (guard : MultiproofConeRootGuard.sourceRoot root physical out=true) :
 reference.verify_owned D hash root s physical=.ok (true,out) := by
 have zero : ¬s.n=0#usize := by
   intro h
   have eq := congrArg UScalar.val h
   change s.n.val=0 at eq
   omega
 have large : ¬s.n>16#usize := by change ¬s.n.val>16;omega
 obtain ⟨rem,rem_run,rem_value⟩ := WP.spec_imp_exists
   (UScalar.rem_spec (x:=Slice.len physical) (y:=32#usize) (by decide))
 have z : rem=0#usize := UScalar.eq_of_val_eq (by
   change rem.val=0
   change rem.val=physical.val.length%32 at rem_value
   omega)
 unfold reference.verify_owned
 simp only [zero,large,if_false,indices,bind_tc_ok,if_true,rem_run,z,show (0#usize != 0#usize)=false from rfl,run]
 exact NNU_MerkleRoot.final root physical out guard
#print axioms returned
end AspisR1.NNU_MerkleWrapper
