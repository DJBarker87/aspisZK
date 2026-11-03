import PV_EVH_Runtime
set_option autoImplicit false
namespace PV_EVHB_WorkerRequests

/-- Source range arithmetic of native_workers::range, before usize encoding.
The 16 worker ranges depend on public n/k; no callback operand is consulted. -/
def range (n k : Nat) : Nat × Nat :=
  let q := n/16
  let r := n%16
  let start := q*k + min k r
  (start,start+q+(if k<r then 1 else 0))

theorem length (n k : Nat) :
    (range n k).2 - (range n k).1 = n/16 + (if k<n%16 then 1 else 0) := by
  unfold range
  dsimp only
  omega

theorem within_public_count (n k : Nat) (worker : k<16) :
    (range n k).1 ≤ (range n k).2 ∧ (range n k).2 ≤ n := by
  have splitn := Nat.mod_add_div n 16
  have small : n%16<16 := Nat.mod_lt n (by omega)
  have mulbound : n/16*(k+1) ≤ n/16*16 :=
    Nat.mul_le_mul_left (n/16) (by omega)
  unfold range
  dsimp only
  by_cases h : k<n%16
  · rw [if_pos h,Nat.min_eq_left (by omega)]
    constructor <;> omega
  · rw [if_neg h,Nat.min_eq_right (by omega)]
    constructor <;> omega

/-- Explicit Vec::with_capacity requests in host_work::map. Other allocations
inside std::thread/TLS/collect and metadata validity remain named V400/rdea-2
obligations; this list is not a fabricated complete resource trace. -/
def explicitCapacities (n : Nat) : List Nat :=
  (List.range 16).map (fun k => (range n k).2 - (range n k).1) ++ [n]

theorem public_byte_requests (n width : Nat) :
    (explicitCapacities n).map (fun cap => cap*width) =
      ((List.range 16).map (fun k => (n/16+(if k<n%16 then 1 else 0))*width)) ++ [n*width] := by
  simp only [explicitCapacities,List.map_append,List.map_map,length,List.map_cons,List.map_nil]

#print axioms length
#print axioms within_public_count
#print axioms public_byte_requests
end PV_EVHB_WorkerRequests
