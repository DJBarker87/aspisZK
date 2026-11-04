import NET_GeometryAllocation
set_option autoImplicit false
namespace NET_GeometryGather

/-- Ordered observations on the SAME two evolving buffers. The native
existence/physical association of each observation remains a separate gate. -/
inductive Trace {T : Type} : List (List T × T) → List T → List T → List T → List T → Prop
 | done (flat lines : List T) : Trace [] flat lines flat lines
 | step (row : List T × T) (rows : List (List T × T))
     (flat lines nextFlat nextLines finalFlat finalLines : List T)
     (flatStep : nextFlat = flat ++ row.1)
     (lineStep : nextLines = lines ++ [row.2]) (width : row.1.length = 5)
     (tail : Trace rows nextFlat nextLines finalFlat finalLines) :
     Trace (row::rows) flat lines finalFlat finalLines

/-- No independently chosen whole-buffer output appears as a premise. -/
theorem meaning {T : Type} {rows : List (List T × T)}
    {flat lines finalFlat finalLines : List T}
    (trace : Trace rows flat lines finalFlat finalLines) :
    finalFlat = flat ++ rows.flatMap Prod.fst ∧
      finalLines = lines ++ rows.map Prod.snd := by
  induction trace with
  | done => simp
  | step row rows flat lines nextFlat nextLines finalFlat finalLines flatStep lineStep width tail ih =>
    rcases ih with ⟨hf,hl⟩
    constructor
    · rw [hf,flatStep]
      simp only [List.flatMap_cons,List.append_assoc]
    · rw [hl,lineStep]
      simp only [List.map_cons,List.append_assoc,List.singleton_append]

/-- Both counters advance together through every observed query. -/
theorem lengths {T : Type} {rows : List (List T × T)}
    {flat lines finalFlat finalLines : List T}
    (trace : Trace rows flat lines finalFlat finalLines) :
    finalFlat.length = flat.length + 5*rows.length ∧
      finalLines.length = lines.length + rows.length := by
  induction trace with
  | done => simp
  | step row rows flat lines nextFlat nextLines finalFlat finalLines flatStep lineStep width tail ih =>
    rcases ih with ⟨hf,hl⟩
    rw [flatStep,List.length_append,width] at hf
    rw [lineStep,List.length_append,List.length_singleton] at hl
    simp only [List.length_cons]
    constructor <;> omega

/-- Reaching the prefix call after all queries establishes its exact size
on the same gathered value list. This is not native trace existence. -/
theorem prefix_domain {T : Type} {rows : List (List T × T)}
    {finalFlat finalLines : List T} (bound : rows.length ≤ 22)
    (trace : Trace rows [] [] finalFlat finalLines) :
    finalFlat.length = 5*rows.length ∧ finalFlat.length ≤ 110 ∧
      finalLines.length = rows.length := by
  obtain ⟨hf,hl⟩ := lengths trace
  simp only [List.length_nil,Nat.zero_add] at hf hl
  exact ⟨hf,by omega,hl⟩

#print axioms meaning
#print axioms lengths
#print axioms prefix_domain
end NET_GeometryGather
