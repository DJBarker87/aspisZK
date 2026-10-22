import R1Z.ProverCommitParentStep44
/-! Eighteen-level parent control, with the complete stored children and
programming/coin history. Leaf hashing and concrete digest-table writes
remain separate callees, not assumed correct by this control theorem. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTree44
open ProverCommitTrustedStd24 ProverCommitParentStep44
variable {Digest Coins State Kids Thread Slot Output : Type}
variable {cmp : Nat → Nat → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

structure Tree (State Kids Coins Digest : Type) where
  level : State
  children : List Kids
  coins : Coins
  reads : Nat
  programmed : List (Digest × Digest × Digest)

def decode (map : MapAPI Nat Digest State cmp)
    (kids : MapAPI Nat (Digest × Digest) Kids cmp) (s : Tree State Kids Coins Digest) :=
  Tree.mk (map.decode s.level) (s.children.map kids.decode) s.coins s.reads s.programmed

def levelStep (map : MapAPI Nat Digest State cmp)
    (kids : MapAPI Nat (Digest × Digest) Kids cmp) (coin : Coins → Digest × Coins)
    (root : Digest) (depth : Nat) (s : Tree State Kids Coins Digest) : Tree State Kids Coins Digest :=
  let initial : Acc State Kids Coins Digest := ⟨map.empty,kids.empty,s.coins,s.reads,s.programmed⟩
  let done := (ProverCommitParents44.native map s.level).foldl
    (step map kids s.level coin root (depth+1==18)) initial
  ⟨done.next,s.children ++ [done.kids],done.coins,done.reads,done.programmed⟩

def levels (map : MapAPI Nat Digest State cmp)
    (kids : MapAPI Nat (Digest × Digest) Kids cmp) (coin : Coins → Digest × Coins)
    (root : Digest) : Nat → Nat → Tree State Kids Coins Digest → Tree State Kids Coins Digest
  | 0,_,s => s
  | n+1,depth,s => levels map kids coin root n (depth+1) (levelStep map kids coin root depth s)

variable [DecidableEq Thread]
variable (map : MapAPI Nat Digest State cmp) (kids : MapAPI Nat (Digest × Digest) Kids cmp)
  (tls : TLSAPI Thread Slot Output) (thread : Thread)
  (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (mapLaw : TrustedStd map tls thread schedule) (kidsLaw : TrustedStd kids tls thread schedule)
include mapLaw kidsLaw

theorem level_decode (coin : Coins → Digest × Coins) (root : Digest)
    (depth : Nat) (s : Tree State Kids Coins Digest) :
    decode map kids (levelStep map kids coin root depth s) =
      levelStep modelMap modelMap coin root depth (decode map kids s) := by
  have h := collected_loop map kids tls thread schedule mapLaw kidsLaw s.level coin root
    (depth+1==18) (Acc.mk map.empty kids.empty s.coins s.reads s.programmed)
  simp only [ProverCommitParentStep44.decode,mapLaw.btree_empty,kidsLaw.btree_empty] at h
  have hn := congrArg Acc.next h
  have hk := congrArg Acc.kids h
  have hc := congrArg Acc.coins h
  have hr := congrArg Acc.reads h
  have hp := congrArg Acc.programmed h
  simp only [ProverCommitParents44.native,modelMap,ProverCommitParents44.model] at hn hk hc hr hp
  simp only [decode,levelStep,List.map_append,List.map_cons,List.map_nil]
  simp only [ProverCommitParents44.native,modelMap,ProverCommitParents44.model] at *
  rw [hn,hk,hc,hr,hp]

theorem levels_decode (coin : Coins → Digest × Coins) (root : Digest)
    (n depth : Nat) (s : Tree State Kids Coins Digest) :
    decode map kids (levels map kids coin root n depth s) =
      levels modelMap modelMap coin root n depth (decode map kids s) := by
  induction n generalizing depth s with
  | zero => rfl
  | succ n ih =>
    rw [levels,ih,level_decode map kids tls thread schedule mapLaw kidsLaw,levels]

omit mapLaw kidsLaw

theorem range_levels (coin : Coins → Digest × Coins) (root : Digest)
    (n depth : Nat) (s : Tree State Kids Coins Digest) :
    (List.range' depth n).foldl (fun state d => levelStep map kids coin root d state) s =
      levels map kids coin root n depth s := by
  induction n generalizing depth s with
  | zero => rfl
  | succ n ih =>
    simpa only [List.range'_succ,Nat.add_one,List.foldl_cons,levels] using
      ih (depth+1) (levelStep map kids coin root depth s)

include mapLaw kidsLaw

theorem eighteen_levels (coin : Coins → Digest × Coins) (root : Digest)
    (s : Tree State Kids Coins Digest) :
    decode map kids ((List.range 18).foldl
      (fun state d => levelStep map kids coin root d state) s) =
      levels modelMap modelMap coin root 18 0 (decode map kids s) := by
  rw [List.range_eq_range',range_levels,levels_decode map kids tls thread schedule mapLaw kidsLaw]

#print axioms level_decode
#print axioms levels_decode
#print axioms range_levels
#print axioms eighteen_levels
end R1Z.ProverCommitTree44
