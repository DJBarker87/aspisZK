import AspisV8R17.IndexSchedule
import AspisV8R17.SourceScatter
import AspisV8R16.BalancedTransport

/-! Concrete 512/513 weighted schedules composed with finite chord reads.
This source-shaped model does not assert extracted Rust field semantics. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [CommRing F]

def sourceEdges (half : F) (n : ℕ) : List (ScatterEdge ℕ ℕ F) :=
  (List.range n).flatMap fun j =>
    ((weightedIndexLoop half 10 j 0 1).getD []).map fun e => (j,e.1,e.2)

theorem sourceEdges_bounds (half : F) (n : ℕ) (h : scheduleBounded n = true)
    (e : ScatterEdge ℕ ℕ F) (he : e ∈ sourceEdges half n) :
    e.1<n ∧ e.2.1<n+1 := by
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp he
  have hjn := List.mem_range.mp hj
  obtain ⟨edges,hw,hb⟩ := weighted_schedule_bounds half n j h hjn
  simp only [hw, Option.getD_some] at he
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  exact ⟨hjn,(hb v hv).1⟩

def sourceChord (half : F) (q : ℕ → F) (a b c : F) (r : ℕ) : F :=
  finiteChordCoefficient 512 (sourceEdges half 512) (sourceEdges half 513) q a b c r

theorem sourceChord_six_constants (half : F) (q s : ℕ → F)
    (a b c t : F) (r : ℕ) :
    sourceChord half (fun i => q i-t*s i) a b c r =
      a*(sourceChord half q 1 0 0 r-t*sourceChord half s 1 0 0 r) +
      b*(sourceChord half q 0 1 0 r-t*sourceChord half s 0 1 0 r) +
      c*(sourceChord half q 0 0 1 r-t*sourceChord half s 0 0 1 r) := by
  exact finite_source_six_constants 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)
    q s a b c t r

theorem active_transport_six_constants (half : F) (inactive : Finset ℕ)
    (pivot r : ℕ) (order : ℕ ≃ ℕ) (hr : r ≠ pivot)
    (q s : ℕ → F) (a b c t : F) :
    let atRow := fun q a b c => AspisV8R16.inverseTransport inactive pivot order
      (sourceChord half q a b c) r
    atRow (fun i => q i-t*s i) a b c =
      a*(atRow q 1 0 0-t*atRow s 1 0 0) +
      b*(atRow q 0 1 0-t*atRow s 0 1 0) +
      c*(atRow q 0 0 1-t*atRow s 0 0 1) := by
  dsimp only
  simp only [AspisV8R16.inverseTransport, if_neg hr]
  exact sourceChord_six_constants half q s a b c t (order.symm r)

theorem scatter_append (xs ys : List (ScatterEdge ℕ ℕ F)) (q : ℕ → F) (r : ℕ) :
    scatterValue (xs++ys) q r = scatterValue xs q r+scatterValue ys q r := by
  simp [scatterValue, List.map_append, List.sum_append]

theorem scatter_column (edges : List (ℕ × F)) (j : ℕ) (q : ℕ → F) (r : ℕ) :
    scatterValue (edges.map fun e => (j,e.1,e.2)) q r =
      q j * (edges.map fun e => if r=e.1 then e.2 else 0).sum := by
  induction edges with
  | nil => simp [scatterValue]
  | cons e es ih =>
      simp only [List.map_cons, scatterValue, List.sum_cons] at ih ⊢
      rw [ih]
      by_cases h : r=e.1 <;> simp only [h, ↓reduceIte] <;> ring

theorem scatter_columns (columns : List ℕ) (edges : ℕ → List (ℕ × F))
    (q : ℕ → F) (r : ℕ) :
    scatterValue (columns.flatMap fun j => (edges j).map fun e => (j,e.1,e.2)) q r =
      (columns.map fun j => q j * ((edges j).map fun e => if r=e.1 then e.2 else 0).sum).sum := by
  induction columns with
  | nil => simp [scatterValue]
  | cons j js ih =>
      simp only [List.flatMap_cons, scatter_append, scatter_column, ih, List.map_cons, List.sum_cons]

theorem range_unit_sum (n j : ℕ) (f : ℕ → F) :
    ((List.range n).map fun i => if i=j then f i else 0).sum = if j<n then f j else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]
      by_cases h : j<n
      · have hn : n≠j := by omega
        have hj : j<n+1 := by omega
        simp [h,hn,hj]
      · by_cases hn : n=j
        · subst j
          simp
        · have hj : ¬j<n+1 := by omega
          simp [h,hn,hj]

theorem sourceScatter_unit (half : F) (n j r : ℕ) (hj : j<n) :
    scatterValue (sourceEdges half n) (fun i => if i=j then 1 else 0) r =
      (((weightedIndexLoop half 10 j 0 1).getD []).map
        fun e => if r=e.1 then e.2 else 0).sum := by
  rw [sourceEdges, scatter_columns]
  simp only [ite_mul, one_mul, zero_mul]
  rw [range_unit_sum, if_pos hj]

def sparseVector (entries : List (ℕ × F)) (i : ℕ) : F :=
  (entries.map fun e => if i=e.1 then e.2 else 0).sum

theorem scatter_sparse (edges : List (ScatterEdge ℕ ℕ F))
    (entries : List (ℕ × F)) (r : ℕ) :
    scatterValue edges (sparseVector entries) r =
      (entries.map fun e => e.2*scatterValue edges (fun i => if i=e.1 then 1 else 0) r).sum := by
  induction entries with
  | nil => simp [sparseVector, scatterValue]
  | cons e es ih =>
      have hs : sparseVector (e::es) = fun i =>
          e.2*(if i=e.1 then 1 else 0)+1*sparseVector es i := by
        funext i
        simp only [sparseVector, List.map_cons, List.sum_cons, one_mul]
        by_cases h : i=e.1 <;> simp [h]
      rw [hs, scatter_value_linear, ih]
      simp

theorem sourceScatter_unit_sparse (half : F) (n j : ℕ) (hj : j<n) :
    scatterValue (sourceEdges half n) (fun i => if i=j then 1 else 0) =
      sparseVector ((weightedIndexLoop half 10 j 0 1).getD []) := by
  funext r
  exact sourceScatter_unit half n j r hj

def unitVector (j i : ℕ) : F := if i=j then 1 else 0

theorem unitVector_even_even (j : ℕ) :
    (fun i => unitVector (F:=F) (2*j) (2*i)) = unitVector j := by
  funext i
  simp [unitVector]

theorem unitVector_even_odd (j : ℕ) :
    (fun i => unitVector (F:=F) (2*j) (2*i+1)) = fun _ => 0 := by
  funext i
  have h : 2*i+1 ≠ 2*j := by omega
  simp [unitVector,h]

theorem unitVector_odd_even (j : ℕ) :
    (fun i => unitVector (F:=F) (2*j+1) (2*i)) = fun _ => 0 := by
  funext i
  have h : 2*i ≠ 2*j+1 := by omega
  simp [unitVector,h]

theorem unitVector_odd_odd (j : ℕ) :
    (fun i => unitVector (F:=F) (2*j+1) (2*i+1)) = unitVector j := by
  funext i
  simp [unitVector]

theorem zeroExtend_unit (n j : ℕ) (hj : j<n) :
    zeroExtend n (unitVector (F:=F) j) = unitVector j := by
  funext i
  by_cases h : i=j
  · subst i; simp [zeroExtend,unitVector,hj]
  · simp [zeroExtend,unitVector,h]

theorem scatter_zero (edges : List (ScatterEdge ℕ ℕ F)) (r : ℕ) :
    scatterValue edges (fun _ => 0) r = 0 := by
  simp [scatterValue]

theorem scatter_zero_function (edges : List (ScatterEdge ℕ ℕ F)) :
    scatterValue edges (fun _ => 0) = fun _ => 0 := by
  funext r
  exact scatter_zero edges r

def sparseX (half : F) (j r : ℕ) : F :=
  sparseVector ((weightedIndexLoop half 10 j 0 1).getD []) r

def sparseXX (half : F) (j r : ℕ) : F :=
  (((weightedIndexLoop half 10 j 0 1).getD []).map fun e => e.2*sparseX half e.1 r).sum

theorem sourceScatter_twice_unit (half : F) (j r : ℕ) (hj : j<512) :
    scatterValue (sourceEdges half 513)
      (scatterValue (sourceEdges half 512) (unitVector j)) r = sparseXX half j r := by
  unfold unitVector
  rw [sourceScatter_unit_sparse half 512 j hj,scatter_sparse]
  unfold sparseXX
  apply congrArg (fun xs : List F => xs.sum)
  apply List.map_congr_left
  intro e he
  obtain ⟨edges,hw,hb⟩ := weighted_schedule_bounds half 512 j schedule512_bounded hj
  have hem : e ∈ edges := by simpa [hw] using he
  rw [sourceScatter_unit half 513 e.1 r (hb e hem).1]
  rfl

theorem sourceChord_unit_even (half : F) (j r : ℕ) (hj : j<512) (a b c : F) :
    sourceChord half (unitVector (2*j)) a b c r =
      if r%2=0 then a*unitVector j (r/2)+b*sparseX half j (r/2)
      else c*unitVector j (r/2) := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [zeroExtend_unit 1024 (2*j) (by omega)]
  simp only [chordCoefficient, chordEven, chordOdd,
    unitVector_even_even, unitVector_even_odd, scatter_zero_function, scatter_zero, mul_zero, sub_zero, add_zero]
  have hs : scatterValue (sourceEdges half 512) (unitVector j) (r/2) = sparseX half j (r/2) :=
    sourceScatter_unit half 512 j (r/2) hj
  rw [hs]
  have hodd : 2*(r/2)+1 ≠ 2*j := by omega
  simp [unitVector,hodd]

theorem sourceChord_unit_odd (half : F) (j r : ℕ) (hj : j<512) (a b c : F) :
    sourceChord half (unitVector (2*j+1)) a b c r =
      if r%2=0 then c*(unitVector j (r/2)-sparseXX half j (r/2))
      else a*unitVector j (r/2)+b*sparseX half j (r/2) := by
  unfold sourceChord
  rw [finiteChordCoefficient_eq 512 _ _
    (fun e he => (sourceEdges_bounds half 512 schedule512_bounded e he).2)
    (fun e he => (sourceEdges_bounds half 513 schedule513_bounded e he).2)]
  rw [zeroExtend_unit 1024 (2*j+1) (by omega)]
  simp only [chordCoefficient, chordEven, chordOdd,
    unitVector_odd_even, unitVector_odd_odd, scatter_zero, mul_zero, zero_add]
  rw [sourceScatter_twice_unit half j (r/2) hj]
  have hs : scatterValue (sourceEdges half 512) (unitVector j) (r/2) = sparseX half j (r/2) :=
    sourceScatter_unit half 512 j (r/2) hj
  rw [hs]
  have heven : 2*(r/2) ≠ 2*j+1 := by omega
  simp [unitVector,heven]

#print axioms sourceChord_unit_odd
#print axioms sourceChord_unit_even
#print axioms sourceScatter_twice_unit
#print axioms zeroExtend_unit
#print axioms unitVector_even_even
#print axioms unitVector_even_odd
#print axioms unitVector_odd_even
#print axioms unitVector_odd_odd
#print axioms scatter_sparse
#print axioms sourceScatter_unit_sparse
#print axioms sourceScatter_unit
#print axioms scatter_columns
#print axioms range_unit_sum
#print axioms active_transport_six_constants
#print axioms sourceEdges_bounds
#print axioms sourceChord_six_constants
end AspisV8R17
