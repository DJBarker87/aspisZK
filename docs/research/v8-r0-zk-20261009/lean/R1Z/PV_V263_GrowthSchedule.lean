import R1Z.PV_V263_RawGrowth
/-! Exact requested capacities for the fifteen handle pushes, conditional
only on the public handle element size class. These are RawVec requests,
not OS allocations: Global::grow may implement a reallocation internally. -/
set_option autoImplicit false
namespace R1Z.PV_V263_GrowthSchedule
open PV_V263_RawGrowth

def nextCap (size length cap : Nat) : Nat :=
  if length=cap then requestedCap size cap else cap

def requests (size : Nat) : Nat → Nat → Nat → List Nat
  | 0,_,_ => []
  | remaining+1,length,cap =>
      let next := nextCap size length cap
      (if length=cap then [next] else []) ++ requests size remaining (length+1) next

/-- Public-sized handles with 2..1024 bytes request capacity 4,8,16. The
twelve other pushes require no growth. No witness or handle payload occurs. -/
theorem moderate (size : Nat) (notOne : size≠1) (small : size≤1024) :
    requests size 15 0 0=[4,8,16] := by
  simp only [requests,nextCap,requestedCap,minCap,if_neg notOne,if_pos small]
  decide

theorem singleByte : requests 1 15 0 0=[8,16] := by decide

theorem large (size : Nat) (largeSize : 1024<size) :
    requests size 15 0 0=[1,2,4,8,16] := by
  have notOne : size≠1 := by omega
  have notSmall : ¬size≤1024 := by omega
  simp only [requests,nextCap,requestedCap,minCap,if_neg notOne,if_neg notSmall]
  decide

theorem same_size (size size' : Nat) (same : size=size') (count length cap : Nat) :
    requests size count length cap=requests size' count length cap := by rw [same]

#print axioms nextCap
#print axioms requests
#print axioms moderate
#print axioms singleByte
#print axioms large
#print axioms same_size
end R1Z.PV_V263_GrowthSchedule
