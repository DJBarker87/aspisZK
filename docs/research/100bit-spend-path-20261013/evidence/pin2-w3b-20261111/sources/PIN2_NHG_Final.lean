import PIN2_PublicBytesRefinement

/-! PIN2 W3b (2026-11-11). Final PIN2 forms of the NHG_* serializer length and
offset theorems, stated over the re-extracted PIN2 carrier `q` and its actual
generated `public_bytes`.

* Unchanged statements (same constants, frozen prefix `sourceSteps`): `source`
  (1455/1427), `bound` (1455), `prefix_room` (1455), `words_room` (1455),
  `frontier_room` (815), `field_domain` (1880) and `frontier_domain` (1240).
* Changed: `returned` is now ≤ 1524 (was ≤ 1455); `seed_size` gives the
  `NGX_SemanticRuntime.seed_domain` premise (≤ 57607) used by `digest_domain`.
* New: `tail_room` / `tail_offsets` for the four appended writes.

`digest_domain` itself and `NHG_PublicCarrier.same_execution` / `begin_carrier`
also need `NGX_SemanticRuntime` and the PIN2 extraction of
`r1_semantic::public_transcript`; see the W3b report. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PIN2_NHG_Final
open AspisR1PublicSerializer.FieldsRefinement431 AspisR1PublicSerializer.Whole431
open PIN2_PublicBytesRefinement (NewPublic toOld)

abbrev steps (q : NewPublic) := sourceSteps (toOld q)

theorem source (q : NewPublic) :
    ((steps q).flatMap stepBytes).length =
      match q with | .Transfer _ _ => 1455 | .Withdrawal _ _ => 1427 := by
  have h := PIN2_SerializerLengths.prefix_length (toOld q)
  cases q <;> exact h

theorem bound (q : NewPublic) : ((steps q).flatMap stepBytes).length ≤ 1455 := by
  rw [source]; cases q <;> simp only <;> omega

/-- PIN2 `returned`: the actual generated producer returns at most 1524 bytes. -/
theorem returned (q : NewPublic) (out : alloc.vec.Vec U8)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok out)) : out.val.length ≤ 1524 := by
  rw [PIN2_PublicBytesRefinement.public_bytes_refines q out h]
  exact PIN2_SerializerLengths.bound _

theorem seed_size (q : NewPublic) (out : alloc.vec.Vec U8)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok out)) : out.val.length ≤ 57607 := by
  have := returned q out h; omega

theorem prefix_room (q : NewPublic) (pre rest : List Step) (s : Step) (out : alloc.vec.Vec U8)
    (same : pre ++ s :: rest = steps q) (bytes : out.val = pre.flatMap stepBytes) :
    out.length + (stepBytes s).length ≤ 1455 :=
  PIN2_SerializerLengths.prefix_room (toOld q) pre rest s out.val same bytes

theorem first (q : NewPublic) : ∃ b rest, steps q = Step.byte b :: rest := by
  cases q <;> exact ⟨_, _, rfl⟩

theorem prefix_nonempty (q : NewPublic) (pre rest : List Step) (s : Step)
    (same : pre ++ s :: rest = steps q) (entered : pre ≠ []) :
    1 ≤ (pre.flatMap stepBytes).length := by
  obtain ⟨b, tail, head⟩ := first q
  cases pre with
  | nil => exact False.elim (entered rfl)
  | cons x xs =>
    rw [head] at same
    change x :: (xs ++ s :: rest) = Step.byte b :: tail at same
    have hx := (List.cons.inj same).1
    rw [hx]
    simp only [List.flatMap_cons, stepBytes, List.length_append, List.length_cons, List.length_nil]
    omega

theorem words_noninitial (q : NewPublic) (pre rest : List Step) (v : Slice U32)
    (same : pre ++ Step.words v :: rest = steps q) : pre ≠ [] := by
  intro empty; subst pre
  obtain ⟨b, tail, head⟩ := first q
  rw [head] at same
  cases (List.cons.inj same).1

theorem frontier_noninitial (q : NewPublic) (pre rest : List Step)
    (v : Array (Array U32 8#usize) 20#usize)
    (same : pre ++ Step.frontier v :: rest = steps q) : pre ≠ [] := by
  intro empty; subst pre
  obtain ⟨b, tail, head⟩ := first q
  rw [head] at same
  cases (List.cons.inj same).1

theorem words_room (q : NewPublic) (pre rest : List Step) (v : Slice U32)
    (out : alloc.vec.Vec U8) (same : pre ++ Step.words v :: rest = steps q)
    (bytes : out.val = pre.flatMap stepBytes) :
    1 ≤ out.val.length ∧ out.val.length + 4 * v.length ≤ 1455 := by
  have room := prefix_room q pre rest (.words v) out same bytes
  have nonempty := prefix_nonempty q pre rest (.words v) same (words_noninitial q pre rest v same)
  rw [← bytes] at nonempty
  change out.val.length + (stepBytes (.words v)).length ≤ 1455 at room
  refine ⟨nonempty, ?_⟩
  simpa only [stepBytes, JFs_SerializerLengths.words] using room

theorem frontier_room (q : NewPublic) (pre rest : List Step)
    (v : Array (Array U32 8#usize) 20#usize) (out : alloc.vec.Vec U8)
    (same : pre ++ Step.frontier v :: rest = steps q) (bytes : out.val = pre.flatMap stepBytes) :
    1 ≤ out.val.length ∧ out.val.length ≤ 815 := by
  have room := prefix_room q pre rest (.frontier v) out same bytes
  have nonempty := prefix_nonempty q pre rest (.frontier v) same (frontier_noninitial q pre rest v same)
  rw [← bytes] at nonempty
  have width : (stepBytes (.frontier v)).length = 640 := JFs_SerializerLengths.frontier_bytes v
  change out.val.length + (stepBytes (.frontier v)).length ≤ 1455 at room
  rw [width] at room
  exact ⟨nonempty, by omega⟩

def Small : Step → Prop
  | .words s => s.length ≤ 8
  | _ => True

theorem single_width (x : U32) : (single x).length ≤ 8 := by
  change (1 : Nat) ≤ 8
  decide

theorem widths (q : NewPublic) : ∀ s ∈ steps q, Small s := by
  cases q <;> intro s member <;>
    simp only [steps, toOld, sourceSteps, tailSteps,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with (h|h|h|h|h|h|h|h) | (h|h|h|h) <;> subst s <;>
    first | trivial | exact Nat.le_of_eq (PIN2_SerializerLengths.digest _) | exact single_width _

theorem field_domain (q : NewPublic) (pre rest : List Step)
    (v : Slice U32) (out : alloc.vec.Vec U8)
    (same : pre ++ Step.words v :: rest = steps q)
    (bytes : out.val = pre.flatMap stepBytes) :
    1 ≤ out.val.length ∧ v.length ≤ 8 ∧ out.val.length + 4 * v.length ≤ 1880 := by
  obtain ⟨nonempty, room⟩ := words_room q pre rest v out same bytes
  have member : Step.words v ∈ steps q := by rw [← same]; simp
  exact ⟨nonempty, widths q (.words v) member, by omega⟩

theorem frontier_domain (q : NewPublic) (pre rest : List Step)
    (v : Array (Array U32 8#usize) 20#usize) (out : alloc.vec.Vec U8)
    (same : pre ++ Step.frontier v :: rest = steps q)
    (bytes : out.val = pre.flatMap stepBytes) :
    1 ≤ out.val.length ∧ out.val.length ≤ 1240 := by
  have bounds := frontier_room q pre rest v out same bytes
  exact ⟨bounds.1, by omega⟩

/-- Room for every appended binding write of the actual PIN2 body. -/
theorem tail_room (q : NewPublic) (pre post : List U8)
    (same : pre ++ post = PIN2_SerializerLengths.tailBytes (toOld q)) :
    ((steps q).flatMap stepBytes ++ pre).length + post.length ≤ 1524 :=
  PIN2_SerializerLengths.tail_room (toOld q) pre post same

/-- Exact output and offsets of a successful PIN2 run: frozen prefix, then
pool, deployment domain, has_destination and (withdrawal) destination. -/
theorem returned_layout (q : NewPublic) (out : alloc.vec.Vec U8)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok out)) :
    out.val.take (PIN2_SerializerLengths.oldLength (toOld q)) = (steps q).flatMap stepBytes ∧
    out.val.drop (PIN2_SerializerLengths.oldLength (toOld q)) =
      PIN2_SerializerLengths.tailBytes (toOld q) := by
  rw [PIN2_PublicBytesRefinement.public_bytes_refines q out h]
  exact ⟨PIN2_SerializerLengths.prefix_preserved _, PIN2_SerializerLengths.tail_at_old_length _⟩

#print axioms source
#print axioms bound
#print axioms returned
#print axioms seed_size
#print axioms prefix_room
#print axioms words_room
#print axioms frontier_room
#print axioms widths
#print axioms field_domain
#print axioms frontier_domain
#print axioms tail_room
#print axioms returned_layout
end AspisR1.PIN2_NHG_Final
