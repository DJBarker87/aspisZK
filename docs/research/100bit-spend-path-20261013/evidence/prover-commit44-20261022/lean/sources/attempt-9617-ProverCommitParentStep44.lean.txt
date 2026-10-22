import R1Z.ProverCommitParents44
/-! Stateful parent caller. The pure digest callee is represented by the
complete ordered (answer,left,right) programming log. A concrete source hash
and publication theorem must consume this log; this file alone is not that
source certificate. -/
set_option autoImplicit false
namespace R1Z.ProverCommitParentStep44
open ProverCommitTrustedStd24
variable {Digest Coins State Kids Thread Slot Output : Type}
variable {cmp : Nat → Nat → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

structure Acc (State Kids Coins Digest : Type) where
  next : State
  kids : Kids
  coins : Coins
  reads : Nat
  programmed : List (Digest × Digest × Digest)

def child (get : Nat → Option Digest) (coin : Coins → Digest × Coins)
    (coins : Coins) (i : Nat) : Digest × Coins :=
  match get i with
  | some d => (d,coins)
  | none => coin coins

def step (map : MapAPI Nat Digest State cmp)
    (kids : MapAPI Nat (Digest × Digest) Kids cmp) (level : State)
    (coin : Coins → Digest × Coins) (root : Digest) (last : Bool)
    (state : Acc State Kids Coins Digest) (p : Nat) : Acc State Kids Coins Digest :=
  let left := child (map.get level) coin state.coins (2*p)
  let right := child (map.get level) coin left.2 (2*p+1)
  let answer := if last then (root,right.2) else coin right.2
  ⟨(map.insert state.next p answer.1).1,
    (kids.insert state.kids p (left.1,right.1)).1,answer.2,state.reads+1,
    state.programmed ++ [(answer.1,left.1,right.1)]⟩

def decode (map : MapAPI Nat Digest State cmp)
    (kids : MapAPI Nat (Digest × Digest) Kids cmp) (state : Acc State Kids Coins Digest) :=
  Acc.mk (map.decode state.next) (kids.decode state.kids) state.coins state.reads state.programmed

variable [DecidableEq Thread]
variable (map : MapAPI Nat Digest State cmp) (kids : MapAPI Nat (Digest × Digest) Kids cmp)
  (tls : TLSAPI Thread Slot Output) (thread : Thread)
  (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (mapLaw : TrustedStd map tls thread schedule) (kidsLaw : TrustedStd kids tls thread schedule)
include mapLaw kidsLaw

theorem step_decode (level : State) (coin : Coins → Digest × Coins) (root : Digest)
    (last : Bool) (state : Acc State Kids Coins Digest) (p : Nat) :
    decode map kids (step map kids level coin root last state p) =
      step modelMap modelMap (map.decode level) coin root last (decode map kids state) p := by
  simp only [decode,step,child,mapLaw.btree_get,mapLaw.btree_insert_state,
    kidsLaw.btree_insert_state,modelMap,ProverCommitTreeOps23.treeInsert]

/-- The parent loop carries both native maps, every previous programming
request and the same coin continuation across all ascending parents. -/
theorem loop_decode (level : State) (coin : Coins → Digest × Coins) (root : Digest)
    (last : Bool) (state : Acc State Kids Coins Digest) (parents : List Nat) :
    decode map kids (parents.foldl (step map kids level coin root last) state) =
      parents.foldl (step modelMap modelMap (map.decode level) coin root last)
        (decode map kids state) := by
  induction parents generalizing state with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons,ih,List.foldl_cons,step_decode map kids tls thread schedule mapLaw kidsLaw]

/-- Install the D156 native collector and its exact iterator order; no
additional parent-caller or coin law is assumed. -/
theorem collected_loop (level : State) (coin : Coins → Digest × Coins) (root : Digest)
    (last : Bool) (state : Acc State Kids Coins Digest) :
    decode map kids ((ProverCommitParents44.native map level).foldl
      (step map kids level coin root last) state) =
      (ProverCommitParents44.model (map.decode level).toList).foldl
        (step modelMap modelMap (map.decode level) coin root last) (decode map kids state) := by
  rw [loop_decode map kids tls thread schedule mapLaw kidsLaw,
    ProverCommitParents44.exact_order map tls thread schedule mapLaw]

omit mapLaw kidsLaw
/-- Source usize arithmetic cannot wrap in a binary parent of the 2^18
leaf domain. This is symbolic arithmetic, with no large finite enumeration. -/
theorem child_index_bound (p s : Nat) (hp : p < 2^17) (hs : s < 2) :
    2*p+s < 2^18 := by omega

#print axioms step_decode
#print axioms loop_decode
#print axioms collected_loop
#print axioms child_index_bound
end R1Z.ProverCommitParentStep44
