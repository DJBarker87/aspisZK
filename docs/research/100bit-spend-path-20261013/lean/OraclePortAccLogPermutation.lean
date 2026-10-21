import RawCutRecordedWordsExecutableBin
import OracleDecisionMultiTree

/-! The precise height-three parent permutation is not an unconditional
invariance of the real first-match recovery primitive. This deliberately
includes a collision, since AcceptedRunJoin has no collision-free antecedent.
It is a recovery-table counterexample, not a full protocol proof. -/
set_option autoImplicit false
namespace AspisR1.OraclePortAccLogPermutation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree BinMerkleTable BinMerkle32Path

def d (n : AspisV8R19.DuplexFrames.Byte) : State := fun _ => n

def A : Children × State := (children (d 0) (d 1),d 8)
def B : Children × State := (children (d 2) (d 3),d 9)
def C : Children × State := (children (d 8) (d 9),d 10)
def D : Children × State := (children (d 4) (d 5),d 10)
def E : Children × State := (children (d 6) (d 7),d 11)
def F : Children × State := (children (d 10) (d 11),d 12)
def G : Children × State := (children (d 10) (d 12),d 13)

/-- Full binary height three: four bottom parents, two middle, one root. -/
def level : Nodes := [A,B,D,E,C,F,G]
/-- Recursive left subtree, recursive right subtree, then root. -/
def recursive : Nodes := [A,B,C,D,E,F,G]

theorem same_multiset : level.Perm recursive := by
  exact List.Perm.cons A (List.Perm.cons B
    ((List.Perm.cons D (List.Perm.swap C E [F,G])).trans
      (List.Perm.swap C D [E,F,G])))

theorem digest_ne {m n : AspisV8R19.DuplexFrames.Byte} (h : m ≠ n) : d m ≠ d n := by
  intro eq
  exact h (congrFun eq 0)

def recoveredLeaves : BinMerkleLeafRecovery.Leaves :=
  [(([],List.replicate 32 0),d 0),(([],List.replicate 32 1),d 4)]

/-- At the common root and same three-edge path, C/D's collision changes the
first matching parent. No commitment boundary is crossed by the permutation. -/
theorem digest_eq (m n : AspisV8R19.DuplexFrames.Byte) : d m = d n ↔ m = n := by
  constructor
  · intro eq; exact congrFun eq 0
  · intro eq; rw [eq]

theorem level_recovers :
    BinMerkleLeafRecovery.recover level recoveredLeaves [0,0,0] (d 13) = none := by
  simp [BinMerkleLeafRecovery.recover,walk,lookup,level,A,B,C,D,E,F,G,
    digest_eq,children]

theorem recursive_recovers :
    BinMerkleLeafRecovery.recover recursive recoveredLeaves [0,0,0] (d 13) =
      some ([],List.replicate 32 0) := by
  simp [BinMerkleLeafRecovery.recover,walk,lookup,recursive,A,B,C,D,E,F,G,
    digest_eq,children,recoveredLeaves,BinMerkleLeafRecovery.lookupLeaf]

theorem recovery_not_invariant : level.Perm recursive ∧
    BinMerkleLeafRecovery.recover level recoveredLeaves [0,0,0] (d 13) ≠
      BinMerkleLeafRecovery.recover recursive recoveredLeaves [0,0,0] (d 13) := by
  refine ⟨same_multiset,?_⟩
  rw [level_recovers,recursive_recovers]
  simp only [ne_eq,reduceCtorEq,not_false_eq_true]

#print axioms same_multiset
#print axioms digest_ne
#print axioms digest_eq
#print axioms level_recovers
#print axioms recursive_recovers
#print axioms recovery_not_invariant
end AspisR1.OraclePortAccLogPermutation
