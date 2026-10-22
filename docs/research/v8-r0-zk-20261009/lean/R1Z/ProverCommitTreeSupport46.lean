import R1Z.ProverCommitTree44
/-! Support invariant for the stored children. Root equality alone is not a
membership certificate for the native BTreeMap Index callback. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTreeSupport46
open ProverCommitTrustedStd24 ProverCommitParentStep44 ProverCommitTree44
variable {Digest Coins : Type}
abbrev Map (V : Type) := Std.TreeMap Nat V compare

def support {V : Type} (map : Map V) : Set Nat := {q | q ∈ map}
def parents (s : Set Nat) : Set Nat := {q | ∃ i ∈ s, i/2=q}

theorem step_next (level : Map Digest) (coin : Coins → Digest × Coins)
    (root : Digest) (last : Bool) (s : Acc (Map Digest) (Map (Digest × Digest)) Coins Digest)
    (p q : Nat) :
    q ∈ (step modelMap modelMap level coin root last s p).next ↔ q=p ∨ q∈s.next := by
  simp [step,modelMap,ProverCommitTreeOps23.treeInsert]
  exact or_congr eq_comm Iff.rfl

theorem step_kids (level : Map Digest) (coin : Coins → Digest × Coins)
    (root : Digest) (last : Bool) (s : Acc (Map Digest) (Map (Digest × Digest)) Coins Digest)
    (p q : Nat) :
    q ∈ (step modelMap modelMap level coin root last s p).kids ↔ q=p ∨ q∈s.kids := by
  simp [step,modelMap,ProverCommitTreeOps23.treeInsert]
  exact or_congr eq_comm Iff.rfl

theorem loop_support (level : Map Digest) (coin : Coins → Digest × Coins)
    (root : Digest) (last : Bool) (s : Acc (Map Digest) (Map (Digest × Digest)) Coins Digest)
    (ps : List Nat) (q : Nat) :
    (q ∈ (ps.foldl (step modelMap modelMap level coin root last) s).next ↔ q∈ps ∨ q∈s.next) ∧
    (q ∈ (ps.foldl (step modelMap modelMap level coin root last) s).kids ↔ q∈ps ∨ q∈s.kids) := by
  induction ps generalizing s with
  | nil => simp only [List.foldl_nil,List.not_mem_nil,false_or,and_self]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have h := ih (step modelMap modelMap level coin root last s p)
    rw [h.1,h.2,step_next,step_kids]
    simp only [List.mem_cons]
    tauto

/-- Keys of the distinct ordered parent collector are precisely the image
of current level keys under division by two. -/
theorem collected (level : Map Digest) (q : Nat) :
    q ∈ ProverCommitParents44.native modelMap level ↔ q ∈ parents (support level) := by
  rw [ProverCommitParents44.native]
  simp only [modelMap,ProverCommitParents44.input,ascendingDistinct,
    Finset.mem_sort,List.mem_toFinset,List.mem_map,parents,support,Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨i,v⟩,mem,rfl⟩
    have hv := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp mem
    exact ⟨i,by simpa only [Std.TreeMap.mem_iff_isSome_getElem?,hv] using (show (some v).isSome=true from rfl),rfl⟩
  · rintro ⟨i,mem,rfl⟩
    cases hv : level[i]? with
    | none => simp only [Std.TreeMap.mem_iff_isSome_getElem?,hv,Option.isSome_none,Bool.false_eq_true] at mem
    | some v => exact ⟨(i,v),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hv,rfl⟩

def made (coin : Coins → Digest × Coins) (root : Digest) (depth : Nat)
    (s : Tree (Map Digest) (Map (Digest × Digest)) Coins Digest) :=
  (ProverCommitParents44.native modelMap s.level).foldl
    (step modelMap modelMap s.level coin root (depth+1==18))
      (Acc.mk (∅ : Map Digest) (∅ : Map (Digest × Digest)) s.coins s.reads s.programmed)

theorem made_support (coin : Coins → Digest × Coins) (root : Digest) (depth : Nat)
    (s : Tree (Map Digest) (Map (Digest × Digest)) Coins Digest) (q : Nat) :
    (q ∈ (made coin root depth s).next ↔ q ∈ parents (support s.level)) ∧
    (q ∈ (made coin root depth s).kids ↔ q ∈ parents (support s.level)) := by
  have h := loop_support s.level coin root (depth+1==18)
    (Acc.mk (∅ : Map Digest) (∅ : Map (Digest × Digest)) s.coins s.reads s.programmed)
    (ProverCommitParents44.native modelMap s.level) q
  simpa [made,collected] using h

theorem level_support (coin : Coins → Digest × Coins) (root : Digest) (depth : Nat)
    (s : Tree (Map Digest) (Map (Digest × Digest)) Coins Digest) :
    support (levelStep modelMap modelMap coin root depth s).level = parents (support s.level) ∧
    (levelStep modelMap modelMap coin root depth s).children.map support =
      s.children.map support ++ [parents (support s.level)] := by
  have hn : support (made coin root depth s).next = parents (support s.level) := by
    ext q;exact (made_support coin root depth s q).1
  have hk : support (made coin root depth s).kids = parents (support s.level) := by
    ext q;exact (made_support coin root depth s q).2
  constructor
  · exact hn
  · change (s.children ++ [(made coin root depth s).kids]).map support = _
    rw [List.map_append,List.map_cons,List.map_nil,hk]

def shape : Nat → Set Nat → List (Set Nat)
  | 0,_ => []
  | n+1,s => parents s :: shape n (parents s)

/-- Every stored child-map domain, in exact depth order, follows from the
actual parent fold. This is stronger than the final root-return guard. -/
theorem children_support (coin : Coins → Digest × Coins) (root : Digest)
    (n depth : Nat) (s : Tree (Map Digest) (Map (Digest × Digest)) Coins Digest) :
    (levels modelMap modelMap coin root n depth s).children.map support =
      s.children.map support ++ shape n (support s.level) := by
  induction n generalizing depth s with
  | zero => simp only [levels,shape,List.append_nil]
  | succ n ih =>
    rw [levels,ih]
    have h := level_support coin root depth s
    rw [h.1,h.2]
    simp only [shape,List.append_assoc,List.singleton_append]

#print axioms made_support
#print axioms level_support
#print axioms children_support
#print axioms step_next
#print axioms step_kids
#print axioms loop_support
#print axioms collected
end R1Z.ProverCommitTreeSupport46
