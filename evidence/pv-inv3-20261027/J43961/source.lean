import R1Z.PV_Inv_BankSource
set_option autoImplicit false
namespace R1Z.PV_Inv_BankPattern
open R0P PV_Inv_BankSource
variable {K : Type} [Field K]

/-- Finite descriptor adapter. Identifying a native tuple with this descriptor
is an input equation, not a consequence of its row number alone. -/
def descriptor (e : CopyEndpoint) : Tuple K :=
  ⟨e.row, fun i => let p := copyPatterns e.pattern
    if p.kinds i = 1 then .cell (bankAt e.row) (p.columns i) e.row (p.offsets i : K)
    else .zero⟩

def BankJoin (banks : Banks K) (t : Trace K) : Prop :=
  ∀ (c : Fin 16) (r : Fin 1024), merged banks c r = t (Fin.castLE (by omega) c) r

theorem limb (banks : Banks K) (t : Trace K) (join : BankJoin banks t)
    (e : CopyEndpoint) (i : Fin 16) :
    read banks ((descriptor (K := K) e).limbs i) =
      copyPatternTuple (copyPatterns e.pattern)
        (fun c => t (Fin.castLE (by omega) c) e.row) i := by
  unfold descriptor copyPatternTuple
  dsimp only
  split
  · rw [cell_read,join]
  · rfl

theorem tuple (banks : Banks K) (t : Trace K) (join : BankJoin banks t)
    (e : CopyEndpoint) :
    value banks (descriptor e) = (copyEndpointTuple t 0 e).2 := by
  funext i
  exact limb banks t join e i

#print axioms limb
#print axioms tuple
end R1Z.PV_Inv_BankPattern
