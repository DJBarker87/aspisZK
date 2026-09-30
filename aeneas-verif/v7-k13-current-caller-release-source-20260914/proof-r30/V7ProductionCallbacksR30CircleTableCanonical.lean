import V7ProductionSnapshotObserverR28.FunsExternal
import V7CallerCurrentReleaseR26FieldBridge

/-!
# Canonicality certificates for the three production V6 circle tables

Each theorem covers one 16-entry generated source chunk. The table assembly
lemmas only transport these named certificates through list append; they never
normalise the complete 64-entry table at a lookup site.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30CircleTableCanonical

abbrev CanonicalRaw (value : Std.U32) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value

def PairCanonical (pair : Array Std.U32 2#usize) : Prop :=
  CanonicalRaw pair.val[0]! ∧ CanonicalRaw pair.val[1]!

def TableCanonical {N : Std.Usize} (table : Array (Array Std.U32 2#usize) N) : Prop :=
  ∀ pair ∈ table.val, PairCanonical pair

/-- Source certificate for the 16 literal pairs in . -/
private theorem low6_chunk00_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk00.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk00,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem low6_chunk01_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk01.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk01,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem low6_chunk02_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk02.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk02,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem low6_chunk03_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk03.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk03,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem middle6_chunk00_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk00.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk00,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem middle6_chunk01_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk01.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk01,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem middle6_chunk02_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk02.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk02,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem middle6_chunk03_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk03.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk03,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem high6_chunk00_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk00.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk00,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem high6_chunk01_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk01.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk01,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem high6_chunk02_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk02.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk02,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

/-- Source certificate for the 16 literal pairs in . -/
private theorem high6_chunk03_canonical :
    ∀ pair ∈ V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk03.val,
      PairCanonical pair := by
  norm_num [V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk03,
    V7ProductionCallbacksR29.staged_circle_tables.circle_pair, PairCanonical,
    CanonicalRaw, AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem append16_canonical
    (left right : Array (Array Std.U32 2#usize) 16#usize)
    (leftCanonical : TableCanonical left)
    (rightCanonical : TableCanonical right) :
    TableCanonical (V7ProductionCallbacksR29.staged_circle_tables.append16 left right) := by
  intro pair member
  change pair ∈ left.val ++ right.val at member
  rcases List.mem_append.mp member with member | member
  · exact leftCanonical pair member
  · exact rightCanonical pair member

private theorem append32_canonical
    (left right : Array (Array Std.U32 2#usize) 32#usize)
    (leftCanonical : TableCanonical left)
    (rightCanonical : TableCanonical right) :
    TableCanonical (V7ProductionCallbacksR29.staged_circle_tables.append32 left right) := by
  intro pair member
  change pair ∈ left.val ++ right.val at member
  rcases List.mem_append.mp member with member | member
  · exact leftCanonical pair member
  · exact rightCanonical pair member

private theorem whole_table_canonical
    (chunk00 chunk01 chunk02 chunk03 : Array (Array Std.U32 2#usize) 16#usize)
    (canonical00 : TableCanonical chunk00)
    (canonical01 : TableCanonical chunk01)
    (canonical02 : TableCanonical chunk02)
    (canonical03 : TableCanonical chunk03) :
    TableCanonical
      (V7ProductionCallbacksR29.staged_circle_tables.append32
        (V7ProductionCallbacksR29.staged_circle_tables.append16 chunk00 chunk01)
        (V7ProductionCallbacksR29.staged_circle_tables.append16 chunk02 chunk03)) := by
  apply append32_canonical
  · exact append16_canonical chunk00 chunk01 canonical00 canonical01
  · exact append16_canonical chunk02 chunk03 canonical02 canonical03

theorem low6_table_canonical :
    TableCanonical V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_LOW6_WINDOW := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_LOW6_WINDOW
  exact whole_table_canonical
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk00
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk01
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk02
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk03
    low6_chunk00_canonical low6_chunk01_canonical low6_chunk02_canonical
    low6_chunk03_canonical

theorem middle6_table_canonical :
    TableCanonical V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_MIDDLE6_WINDOW := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_MIDDLE6_WINDOW
  exact whole_table_canonical
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk00
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk01
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk02
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_MIDDLE6_WINDOW_chunk03
    middle6_chunk00_canonical middle6_chunk01_canonical middle6_chunk02_canonical
    middle6_chunk03_canonical

theorem high6_table_canonical :
    TableCanonical V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_HIGH6_WINDOW := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_HIGH6_WINDOW
  exact whole_table_canonical
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk00
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk01
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk02
    V7ProductionCallbacksR29.staged_circle_tables.V6_CIRCLE_HIGH6_WINDOW_chunk03
    high6_chunk00_canonical high6_chunk01_canonical high6_chunk02_canonical
    high6_chunk03_canonical

private theorem table_index_canonical
    {N : Std.Usize} (table : Array (Array Std.U32 2#usize) N)
    (canonical : TableCanonical table) (index : Std.Usize)
    (pair : Array Std.U32 2#usize)
    (run : Array.index_usize table index = ok pair) : PairCanonical pair := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i present
    have presentList : table.val[index.val]? = some pair := by
      simpa [Result.ok.inj run] using present
    have bound : index.val < table.val.length := by
      by_contra outOfBounds
      have absent : table.val[index.val]? = none :=
        List.getElem?_eq_none (by omega)
      rw [absent] at presentList
      cases presentList
    have exact : pair = table.val[index.val]! := by
      symm
      exact List.getElem!_of_getElem? presentList
    rw [exact]
    apply canonical (table.val[index.val]!)
    rw [← List.Inhabited_getElem_eq_getElem! table.val index.val bound]
    exact List.getElem_mem bound

theorem low6_lookup_canonical
    (index : Std.Usize) (pair : Array Std.U32 2#usize)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_LOW6_WINDOW.index_usize
      index = ok pair) : PairCanonical pair :=
  table_index_canonical _ low6_table_canonical index pair run

theorem middle6_lookup_canonical
    (index : Std.Usize) (pair : Array Std.U32 2#usize)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_MIDDLE6_WINDOW.index_usize
      index = ok pair) : PairCanonical pair :=
  table_index_canonical _ middle6_table_canonical index pair run

theorem high6_lookup_canonical
    (index : Std.Usize) (pair : Array Std.U32 2#usize)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.V6_CIRCLE_HIGH6_WINDOW.index_usize
      index = ok pair) : PairCanonical pair :=
  table_index_canonical _ high6_table_canonical index pair run

#print axioms low6_table_canonical
#print axioms middle6_table_canonical
#print axioms high6_table_canonical

end V7ProductionCallbacksR30CircleTableCanonical
