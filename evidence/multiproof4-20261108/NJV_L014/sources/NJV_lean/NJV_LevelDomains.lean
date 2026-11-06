import NJV_NativeLevels
import NJV_RowDomains
import NJP_LevelsTotal

set_option autoImplicit false
noncomputable section
namespace NJV_LevelDomains
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel NJP_LoopTotal
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem progress (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (history : List (Request × Digest)) (out : Level)
    (native : NJV_NativeRows.Invocation H nodes length s.n s 0 0 history out)
    (domain : LevelDomain length s) : LevelProgress length s out := by
 obtain ⟨model,returned,valid⟩ := NJP_LevelsTotal.level_total H nodes length s domain
 have observed := congrArg Prod.snd (NJV_NativeRows.observation H nodes length s.n s 0 0 history out native)
 change (eval H (level nodes length s)).2=ok out at observed
 have same := Result.ok.inj (returned.symm.trans observed)
 rw [same] at valid
 exact valid

inductive Admissible (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
    Nat → Scratch → List (Request × Digest) → Level → Prop where
 | final (s : Scratch) (domain : LevelDomain length s) : Admissible H nodes length 0 s [] (.done s)
 | stop (height : Nat) (s after : Scratch) (history : List (Request × Digest))
     (domain : LevelDomain length s)
     (row : NJV_RowDomains.Admissible H nodes length s.n s 0 0 history (.stop after)) :
   Admissible H nodes length (height+1) s history (.stop after)
 | next (height : Nat) (s after : Scratch) (first rest : List (Request × Digest)) (out : Level)
     (domain : LevelDomain length s)
     (row : NJV_RowDomains.Admissible H nodes length s.n s 0 0 first (.done after))
     (tail : Admissible H nodes length height after rest out) :
   Admissible H nodes length (height+1) s (first++rest) out

theorem all (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
    (s : Scratch) (history : List (Request × Digest)) (out : Level)
    (native : NJV_NativeLevels.Invocation H nodes length height s history out)
    (domain : LevelDomain length s) : Admissible H nodes length height s history out := by
 induction native with
 | final s => exact .final s domain
 | stop height s after history row =>
   have rowDomain : Domain length s 0 0 :=
     ⟨domain.1,domain.2.1,by omega,by omega,domain.2.2.1,domain.2.2.2⟩
   exact .stop height s after history domain (NJV_RowDomains.all H nodes length s.n s 0 0 _ _ row rowDomain)
 | next height s after first rest out row tail ih =>
   have rowDomain : Domain length s 0 0 :=
     ⟨domain.1,domain.2.1,by omega,by omega,domain.2.2.1,domain.2.2.2⟩
   have p := progress H nodes length s first (.done after) row domain
   exact .next height s after first rest out domain
     (NJV_RowDomains.all H nodes length s.n s 0 0 _ _ row rowDomain) (ih p.1)

#print progress
#print axioms progress
#print all
#print axioms all
end NJV_LevelDomains
end
