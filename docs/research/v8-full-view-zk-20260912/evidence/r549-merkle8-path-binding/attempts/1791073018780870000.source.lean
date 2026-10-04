import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-! Generic eight-way path binding.  It models literal `0x18 || children`
preimages only; it is not a source-execution or collision-probability result. -/
set_option autoImplicit false
namespace AspisV8R19.R549

abbrev Byte := Fin 256
abbrev Digest := Fin 26 → Byte
abbrev Children := Fin 8 → Digest

/-- The literal child-major payload byte at `8*26` positions. -/
def childByte (children : Children) (i : Fin 208) : Byte :=
  children ⟨i.val / 26, by omega⟩ ⟨i.val % 26, Nat.mod_lt _ (by omega)⟩

def nodeBytes (children : Children) : List Byte := List.ofFn (childByte children)

def nodeInput (children : Children) : List Byte := (0x18 : Byte) :: nodeBytes children

theorem nodeInput_length (children : Children) : (nodeInput children).length = 209 := by
  change 1 + (List.ofFn (childByte children)).length = 209
  rw [List.length_ofFn]

theorem nodeBytes_injective : Function.Injective nodeBytes := by
  intro left right h
  apply funext
  intro child
  apply funext
  intro byte
  have hb := congrFun (List.ofFn_injective h)
    ⟨child.val * 26 + byte.val, by omega⟩
  simpa [nodeBytes, childByte] using hb

theorem nodeInput_injective : Function.Injective nodeInput := by
  intro left right h
  exact nodeBytes_injective (by simpa [nodeInput] using congrArg List.tail h)

/-- Supply eight source-order positions, then replace the selected one by the
running digest.  The supplied value at that slot is ignored; all other seven
positions are retained in their original order. -/
def fillChild (slot : Fin 8) (siblings : Children) (current : Digest) : Children :=
  Function.update siblings slot current

theorem fillChild_ne {slot : Fin 8} {leftSiblings rightSiblings : Children}
    {left right : Digest} (hne : left ≠ right) :
    fillChild slot leftSiblings left ≠ fillChild slot rightSiblings right := by
  intro h
  have hs := congrFun h slot
  exact hne (by simpa [fillChild] using hs)

theorem nodeInput_ne_of_current_ne (slot : Fin 8)
    (leftSiblings rightSiblings : Children) {left right : Digest}
    (hne : left ≠ right) :
    nodeInput (fillChild slot leftSiblings left) ≠
      nodeInput (fillChild slot rightSiblings right) := by
  intro h
  apply fillChild_ne hne
  exact nodeInput_injective h

/-- One complete authentication path, indexed by its full public slot list. -/
inductive Path : List (Fin 8) → Type where
  | nil : Path []
  | cons {slot : Fin 8} {slots : List (Fin 8)}
      (siblings : Children) (tail : Path slots) : Path (slot :: slots)

def foldPath (hash : List Byte → Digest) :
    {slots : List (Fin 8)} → Path slots → Digest → Digest
  | [], .nil, current => current
  | slot :: slots, @Path.cons .(slot) .(slots) siblings tail, current =>
      foldPath hash tail (hash (nodeInput (fillChild slot siblings current)))

def inputTrace (hash : List Byte → Digest) :
    {slots : List (Fin 8)} → Path slots → Digest → List (List Byte)
  | [], .nil, _ => []
  | slot :: slots, @Path.cons .(slot) .(slots) siblings tail, current =>
      let input := nodeInput (fillChild slot siblings current)
      input :: inputTrace hash tail (hash input)

def CrossTraceCollision (hash : List Byte → Digest)
    (leftTrace rightTrace : List (List Byte)) : Prop :=
  ∃ left ∈ leftTrace, ∃ right ∈ rightTrace,
    left ≠ right ∧ hash left = hash right

/-- Different initial digests that reach one root through paths with the same
complete slot list expose a collision between literal node preimages. -/
theorem foldPath_cross_trace_collision {hash : List Byte → Digest} :
    ∀ {slots : List (Fin 8)} (leftPath rightPath : Path slots)
      {left right : Digest}, left ≠ right →
      foldPath hash leftPath left = foldPath hash rightPath right →
      CrossTraceCollision hash (inputTrace hash leftPath left)
        (inputTrace hash rightPath right) := by
  intro slots
  induction slots with
  | nil =>
      intro leftPath rightPath left right hne heq
      cases leftPath
      cases rightPath
      exact False.elim (hne (by simpa [foldPath] using heq))
  | cons slot slots ih =>
      intro leftPath rightPath left right hne heq
      cases leftPath with
      | cons leftSiblings leftTail =>
        cases rightPath with
        | cons rightSiblings rightTail =>
          let leftInput := nodeInput (fillChild slot leftSiblings left)
          let rightInput := nodeInput (fillChild slot rightSiblings right)
          have hinputs : leftInput ≠ rightInput :=
            nodeInput_ne_of_current_ne slot leftSiblings rightSiblings hne
          by_cases hhash : hash leftInput = hash rightInput
          · exact ⟨leftInput, by simp [inputTrace, leftInput],
              rightInput, by simp [inputTrace, rightInput], hinputs, hhash⟩
          · obtain ⟨a, ha, b, hb, hab, heqhash⟩ :=
              ih leftTail rightTail hhash (by
                simpa [foldPath, leftInput, rightInput] using heq)
            exact ⟨a, by
                simp only [inputTrace, List.mem_cons]
                exact Or.inr (by simpa [leftInput] using ha),
              b, by
                simp only [inputTrace, List.mem_cons]
                exact Or.inr (by simpa [rightInput] using hb), hab, heqhash⟩

/-- Collision freedom restricted to the two literal traces. -/
def CollisionFreeOn (hash : List Byte → Digest)
    (leftTrace rightTrace : List (List Byte)) : Prop :=
  ∀ left ∈ leftTrace, ∀ right ∈ rightTrace,
    hash left = hash right → left = right

/-- Under the explicit two-trace noncollision premise, distinct initial
Digests cannot authenticate to the same root. -/
theorem foldPath_injective_of_collisionFreeOn {hash : List Byte → Digest}
    {slots : List (Fin 8)} (leftPath rightPath : Path slots)
    {left right : Digest}
    (hfree : CollisionFreeOn hash (inputTrace hash leftPath left)
      (inputTrace hash rightPath right)) :
    left ≠ right →
    foldPath hash leftPath left ≠ foldPath hash rightPath right := by
  intro hne heq
  obtain ⟨a, ha, b, hb, hab, hh⟩ :=
    foldPath_cross_trace_collision leftPath rightPath hne heq
  exact hab (hfree a ha b hb hh)

/-- The exact six-level specialization for an 8-ary tree with `8^6 = 2^18`
leaves.  The slot list is retained rather than fixed or shortened. -/
theorem depth6_cross_trace_collision {hash : List Byte → Digest}
    (slots : List (Fin 8)) (hdepth : slots.length = 6)
    (leftPath rightPath : Path slots) {left right : Digest}
    (hne : left ≠ right)
    (heq : foldPath hash leftPath left = foldPath hash rightPath right) :
    CrossTraceCollision hash (inputTrace hash leftPath left)
      (inputTrace hash rightPath right) := by
  exact foldPath_cross_trace_collision leftPath rightPath hne heq

#print axioms nodeInput_length
#print axioms nodeBytes_injective
#print axioms nodeInput_injective
#print axioms fillChild_ne
#print axioms nodeInput_ne_of_current_ne
#print axioms foldPath_cross_trace_collision
#print axioms foldPath_injective_of_collisionFreeOn
#print axioms depth6_cross_trace_collision

end AspisV8R19.R549
