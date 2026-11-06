import NKE_CommonProgram
set_option autoImplicit false
noncomputable section
namespace NLT_SiteOrder
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
def rank : Event → Nat
 | .resume .. => 0
 | .powers .. => 1
 | .inactive .. => 2
 | .merkle .. => 3
 | .geometry .. => 4
 | .pending .. => 5
 | .query .. => 6
 | .flush .. => 7
 | .finish .. => 8
/-- Structural source-order certificate covers all possible decoded replies,
not just the seeded/evaluated source run. -/
inductive Shape {A : Type} : Nat → Program Event A → Prop where
 | ret (n : Nat) (value : A) : Shape n (.ret value)
 | prim {B : Type} (n : Nat) (reply : Result B) (next : B → Program Event A)
   (tail : ∀ value,Shape n (next value)) : Shape n (.prim reply next)
 | call {B : Type} (n : Nat) (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (bound : n≤rank (codec.encode seed))
   (tail : ∀ value,Shape (rank (codec.encode seed)+1) (next value)) : Shape n (.call codec seed next)
/-- The nine parent sites occur strictly in source order for arbitrary native
replies. No allocator outcome or callee Result is assumed. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X) :
 Shape 0 (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none) := by
 unfold NKE_CommonProgram.run
 repeat' first
 | (apply Shape.call)
 | (apply Shape.prim)
 | (apply Shape.ret)
 | (intro value)
 | (exact Nat.le_refl _)
 | (exact Nat.zero_le _)
 | (change 1≤1;omega)
 | (change 2≤2;omega)
 | (change 3≤3;omega)
 | (change 4≤4;omega)
 | (change 5≤5;omega)
 | (change 6≤6;omega)
 | (change 7≤7;omega)
 | (change 8≤8;omega)
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
set_option pp.proofs false
#print source
#print axioms source
end NLT_SiteOrder
