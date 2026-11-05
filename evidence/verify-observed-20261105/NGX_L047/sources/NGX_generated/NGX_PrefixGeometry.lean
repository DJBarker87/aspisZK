import NFU_RowDomains
set_option autoImplicit false
namespace AspisR1.NGX_PrefixGeometry

def start (row : Nat) : Nat :=
 if row≤2 then 32+5*row
 else if row≤14 then 64+5*row
 else if row≤25 then 171+901*(row-15) else 12898

def width (row : Nat) : Nat := 5+NFU_PacketDomains.payloadSize row

theorem start_zero : start 0=32 := by rfl

theorem next (row : Nat) (bound : row<26) : start (row+1)=start row+width row := by
 unfold start width NFU_PacketDomains.payloadSize
 repeat' first | (solve | omega) | split

theorem start_bound (row : Nat) (bound : row≤26) : start row≤12898 := by
 unfold start
 split <;> (try omega)
 split <;> (try omega)
 split <;> omega

theorem widths (row : Nat) : 5≤width row ∧ width row≤3717 := by
 have h := NFU_PacketDomains.payload_bound row
 unfold width
 omega

theorem terminal : start 26+width 26=13831 := by rfl

#print axioms start_zero
#print axioms next
#print axioms start_bound
#print axioms widths
#print axioms terminal
end AspisR1.NGX_PrefixGeometry
