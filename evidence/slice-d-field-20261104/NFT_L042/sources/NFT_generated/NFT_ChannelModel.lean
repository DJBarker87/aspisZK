import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_ChannelModel
abbrev Cell := Fin 3 × Fin 3
abbrev State := Cell → Nat

def trace : List Cell := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def step (s : State) (target : Cell) (product : Nat) : State :=
  fun cell => if cell=target then s cell+product else s cell

theorem product_bound (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
    a*b<2^62 := by
  calc
    a*b<2147483647*2147483647 := Nat.mul_lt_mul_of_lt_of_lt ha hb
    _<2^62 := by norm_num

theorem addition_bound (s p : Nat) (hs : s<3*2^62) (hp : p<2^62) :
    s+p<2^64 := by omega

theorem selected (s : State) (cell : Cell) (p : Nat) : step s cell p cell=s cell+p := by
  simp only [step,if_pos rfl]

theorem frame (s : State) (target cell : Cell) (p : Nat) (different : cell≠target) :
    step s target p cell=s cell := by simp only [step,if_neg different]

theorem control : (List.finRange 3).flatMap (fun i => (List.finRange 3).map (fun j => (i,j)))=trace := by rfl

theorem complete (s : State) (products : Cell → Nat) (cell : Cell) :
    (trace.foldl (fun state target => step state target (products target)) s) cell=s cell+products cell := by
  rcases cell with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [trace,step]

#print axioms product_bound
#print axioms addition_bound
#print axioms selected
#print axioms frame
#print axioms control
#print axioms complete
end NFT_ChannelModel
