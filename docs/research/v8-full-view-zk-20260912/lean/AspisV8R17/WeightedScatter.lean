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

#print axioms active_transport_six_constants
#print axioms sourceEdges_bounds
#print axioms sourceChord_six_constants
end AspisV8R17
