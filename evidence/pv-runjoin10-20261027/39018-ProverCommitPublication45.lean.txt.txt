import R1Z.ProverCommitStd45
import R1Z.ProverCommitTree44
import R1Z.ProverCommitMerge33
/-! Guarded tree return and ordered transcript publication. These deterministic
caller equations preserve errors and all retained state. The concrete native
hash/codec/multiproof callees are not postulated by these definitions. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPublication45
open ProverCommitTrustedStd24 ProverCommitTree44
variable {Digest Coins State Kids Thread Slot Output : Type}
variable {cmp : Nat → Nat → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
variable [DecidableEq Thread] [DecidableEq Digest]

def treeReturn (map : MapAPI Nat Digest State cmp) (root : Digest)
    (s : Tree State Kids Coins Digest) : Option (Tree State Kids Coins Digest) :=
  if ProverCommitStd45.rootGuard map s.level root then some s else none

variable (map : MapAPI Nat Digest State cmp) (kids : MapAPI Nat (Digest × Digest) Kids cmp)
  (tls : TLSAPI Thread Slot Output) (thread : Thread)
  (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (mapLaw : TrustedStd map tls thread schedule) (kidsLaw : TrustedStd kids tls thread schedule)
include mapLaw

theorem tree_return (root : Digest) (s : Tree State Kids Coins Digest) :
    (treeReturn map root s).map (decode map kids) =
      treeReturn modelMap root (decode map kids s) := by
  unfold treeReturn
  rw [ProverCommitStd45.root_guard map tls thread schedule mapLaw]
  change (if ProverCommitStd45.rootGuard modelMap (map.decode s.level) root then
    some s else none).map (decode map kids) =
      (if ProverCommitStd45.rootGuard modelMap (map.decode s.level) root then
        some (decode map kids s) else none)
  split <;> rfl

include kidsLaw

/-- The complete eighteen-level owner now includes its final Merkle error
branch, preserving stored children, coins, reads and programming history. -/
theorem guarded_eighteen_levels (coin : Coins → Digest × Coins) (root : Digest)
    (s : Tree State Kids Coins Digest) :
    (treeReturn map root ((List.range 18).foldl
      (fun state d => levelStep map kids coin root d state) s)).map (decode map kids) =
      treeReturn modelMap root (levels modelMap modelMap coin root 18 0 (decode map kids s)) := by
  rw [tree_return map kids tls thread schedule mapLaw,
    eighteen_levels map kids tls thread schedule mapLaw kidsLaw]

omit mapLaw kidsLaw
variable {Key Value Table : Type}
variable {order : Key → Key → Ordering} [Std.TransCmp order] [Std.LawfulEqCmp order]
variable [DecidableEq Value]

/-- Transcript length is observed before first-conflict merge. On a conflict
there is no returned table or read count. -/
def publication (api : MapAPI Key Value Table order) (table transcript : Table) :
    Option (Table × Nat) :=
  (ProverCommitMerge33.loop api (api.entries transcript) table).map
    (fun final => (final,api.len transcript))

variable (api : MapAPI Key Value Table order)
  (law : TrustedStd api tls thread schedule)
include law

theorem publication_decode (table transcript : Table) :
    (publication api table transcript).map (fun p => (api.decode p.1,p.2)) =
      publication modelMap (api.decode table) (api.decode transcript) := by
  have merge := ProverCommitMerge33.native_ordered_loop_decode api tls thread schedule law table transcript
  unfold publication
  rw [Option.map_map]
  rw [law.btree_len]
  have mapped := congrArg (Option.map (fun final => (final,(api.decode transcript).toList.length))) merge
  simpa only [Option.map_map,Function.comp_def,publication,ProverCommitMerge33.loop_recursive,modelMap] using mapped

/-- An error from the merge remains an error; internal overwritten entries
cannot be promoted into a published successful table. -/
theorem publication_none (table transcript : Table) :
    publication api table transcript = none ↔
      publication modelMap (api.decode table) (api.decode transcript) = none := by
  have eq := publication_decode tls thread schedule api law table transcript
  rw [← eq,Option.map_eq_none_iff]

#print axioms tree_return
#print axioms guarded_eighteen_levels
#print axioms publication_decode
#print axioms publication_none
end R1Z.ProverCommitPublication45
