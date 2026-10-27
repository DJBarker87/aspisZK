import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup7019
import R1Z.PV_RunJoin_ValidatorGroup7319
import R1Z.PV_RunJoin_ValidatorGroup7619
import R1Z.PV_RunJoin_ValidatorGroup7919
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,514446081#u32,115798455#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a1 : State := Array.make 16#usize [2130322641#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a2 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a3 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,0#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a4 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,0#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a5 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,0#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a6 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,0#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a7 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,514446081#u32,0#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def a8 : State := Array.make 16#usize [2130322641#u32,1665426257#u32,1206815286#u32,1635654730#u32,225199437#u32,982012671#u32,514446081#u32,115798455#u32,986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,228521044#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7219.s0
  | 1 => PV_RunJoin_ValidatorCell7219.s3
  | 2 => PV_RunJoin_ValidatorCell7219.s5
  | 3 => PV_RunJoin_ValidatorCell7219.s7
  | 4 => PV_RunJoin_ValidatorCell7219.s9
  | 5 => PV_RunJoin_ValidatorCell7219.s11
  | 6 => PV_RunJoin_ValidatorCell7219.s13
  | 7 => PV_RunJoin_ValidatorCell7219.s15
  | 8 => PV_RunJoin_ValidatorCell7219.s17
  | 9 => PV_RunJoin_ValidatorCell7219.s19
  | 10 => PV_RunJoin_ValidatorCell7219.s21
  | 11 => PV_RunJoin_ValidatorCell7219.s23
  | _ => PV_RunJoin_ValidatorCell7219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2130322641#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1665426257#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1206815286#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1635654730#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨225199437#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨982012671#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨514446081#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨115798455#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7219.s2,PV_RunJoin_ValidatorCell7219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s4,PV_RunJoin_ValidatorCell7219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s6,PV_RunJoin_ValidatorCell7219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s8,PV_RunJoin_ValidatorCell7219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s10,PV_RunJoin_ValidatorCell7219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s12,PV_RunJoin_ValidatorCell7219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s14,PV_RunJoin_ValidatorCell7219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s16,PV_RunJoin_ValidatorCell7219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s18,PV_RunJoin_ValidatorCell7219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s20,PV_RunJoin_ValidatorCell7219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7219.s22,PV_RunJoin_ValidatorCell7219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,351180429#u32,2094192877#u32,1421708941#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a1 : State := Array.make 16#usize [87052585#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a2 : State := Array.make 16#usize [87052585#u32,1514049792#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a3 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a4 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,0#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a5 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,0#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a6 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,351180429#u32,0#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a7 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,351180429#u32,2094192877#u32,0#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def a8 : State := Array.make 16#usize [87052585#u32,1514049792#u32,1826519353#u32,387817177#u32,1511331359#u32,351180429#u32,2094192877#u32,1421708941#u32,2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,1001875166#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7319.s0
  | 1 => PV_RunJoin_ValidatorCell7319.s3
  | 2 => PV_RunJoin_ValidatorCell7319.s5
  | 3 => PV_RunJoin_ValidatorCell7319.s7
  | 4 => PV_RunJoin_ValidatorCell7319.s9
  | 5 => PV_RunJoin_ValidatorCell7319.s11
  | 6 => PV_RunJoin_ValidatorCell7319.s13
  | 7 => PV_RunJoin_ValidatorCell7319.s15
  | 8 => PV_RunJoin_ValidatorCell7319.s17
  | 9 => PV_RunJoin_ValidatorCell7319.s19
  | 10 => PV_RunJoin_ValidatorCell7319.s21
  | 11 => PV_RunJoin_ValidatorCell7319.s23
  | _ => PV_RunJoin_ValidatorCell7319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨87052585#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1514049792#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1826519353#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨387817177#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1511331359#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨351180429#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2094192877#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1421708941#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7319.s2,PV_RunJoin_ValidatorCell7319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s4,PV_RunJoin_ValidatorCell7319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s6,PV_RunJoin_ValidatorCell7319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s8,PV_RunJoin_ValidatorCell7319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s10,PV_RunJoin_ValidatorCell7319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s12,PV_RunJoin_ValidatorCell7319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s14,PV_RunJoin_ValidatorCell7319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s16,PV_RunJoin_ValidatorCell7319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s18,PV_RunJoin_ValidatorCell7319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s20,PV_RunJoin_ValidatorCell7319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7319.s22,PV_RunJoin_ValidatorCell7319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,34881120#u32,1632903117#u32,1891593814#u32,1830035060#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a1 : State := Array.make 16#usize [1024910236#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a2 : State := Array.make 16#usize [1024910236#u32,34897137#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a3 : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,0#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a4 : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,0#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a5 : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,34881120#u32,0#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a6 : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,34881120#u32,1632903117#u32,0#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a7 : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,34881120#u32,1632903117#u32,1891593814#u32,0#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def a8 : State := Array.make 16#usize [1024910236#u32,34897137#u32,119525087#u32,2069845639#u32,34881120#u32,1632903117#u32,1891593814#u32,1830035060#u32,260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,2054173171#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7419.s0
  | 1 => PV_RunJoin_ValidatorCell7419.s3
  | 2 => PV_RunJoin_ValidatorCell7419.s5
  | 3 => PV_RunJoin_ValidatorCell7419.s7
  | 4 => PV_RunJoin_ValidatorCell7419.s9
  | 5 => PV_RunJoin_ValidatorCell7419.s11
  | 6 => PV_RunJoin_ValidatorCell7419.s13
  | 7 => PV_RunJoin_ValidatorCell7419.s15
  | 8 => PV_RunJoin_ValidatorCell7419.s17
  | 9 => PV_RunJoin_ValidatorCell7419.s19
  | 10 => PV_RunJoin_ValidatorCell7419.s21
  | 11 => PV_RunJoin_ValidatorCell7419.s23
  | _ => PV_RunJoin_ValidatorCell7419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1024910236#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨34897137#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨119525087#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2069845639#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨34881120#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1632903117#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1891593814#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1830035060#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7419.s2,PV_RunJoin_ValidatorCell7419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s4,PV_RunJoin_ValidatorCell7419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s6,PV_RunJoin_ValidatorCell7419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s8,PV_RunJoin_ValidatorCell7419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s10,PV_RunJoin_ValidatorCell7419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s12,PV_RunJoin_ValidatorCell7419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s14,PV_RunJoin_ValidatorCell7419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s16,PV_RunJoin_ValidatorCell7419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s18,PV_RunJoin_ValidatorCell7419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s20,PV_RunJoin_ValidatorCell7419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7419.s22,PV_RunJoin_ValidatorCell7419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,1378667390#u32,256051405#u32,1303928677#u32,1488857718#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a1 : State := Array.make 16#usize [1669216135#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a2 : State := Array.make 16#usize [1669216135#u32,741703000#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a3 : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a4 : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,0#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a5 : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,1378667390#u32,0#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a6 : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,1378667390#u32,256051405#u32,0#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a7 : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,1378667390#u32,256051405#u32,1303928677#u32,0#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def a8 : State := Array.make 16#usize [1669216135#u32,741703000#u32,562283949#u32,1060793623#u32,1378667390#u32,256051405#u32,1303928677#u32,1488857718#u32,1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,628703965#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7519.s0
  | 1 => PV_RunJoin_ValidatorCell7519.s3
  | 2 => PV_RunJoin_ValidatorCell7519.s5
  | 3 => PV_RunJoin_ValidatorCell7519.s7
  | 4 => PV_RunJoin_ValidatorCell7519.s9
  | 5 => PV_RunJoin_ValidatorCell7519.s11
  | 6 => PV_RunJoin_ValidatorCell7519.s13
  | 7 => PV_RunJoin_ValidatorCell7519.s15
  | 8 => PV_RunJoin_ValidatorCell7519.s17
  | 9 => PV_RunJoin_ValidatorCell7519.s19
  | 10 => PV_RunJoin_ValidatorCell7519.s21
  | 11 => PV_RunJoin_ValidatorCell7519.s23
  | _ => PV_RunJoin_ValidatorCell7519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1669216135#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨741703000#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨562283949#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1060793623#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1378667390#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨256051405#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1303928677#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1488857718#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7519.s2,PV_RunJoin_ValidatorCell7519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s4,PV_RunJoin_ValidatorCell7519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s6,PV_RunJoin_ValidatorCell7519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s8,PV_RunJoin_ValidatorCell7519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s10,PV_RunJoin_ValidatorCell7519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s12,PV_RunJoin_ValidatorCell7519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s14,PV_RunJoin_ValidatorCell7519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s16,PV_RunJoin_ValidatorCell7519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s18,PV_RunJoin_ValidatorCell7519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s20,PV_RunJoin_ValidatorCell7519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7519.s22,PV_RunJoin_ValidatorCell7519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,1837706654#u32,827038403#u32,1892640303#u32,370983584#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a1 : State := Array.make 16#usize [1385985564#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a2 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a3 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a4 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,0#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a5 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,1837706654#u32,0#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a6 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,1837706654#u32,827038403#u32,0#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a7 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,1837706654#u32,827038403#u32,1892640303#u32,0#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def a8 : State := Array.make 16#usize [1385985564#u32,1312452205#u32,34748210#u32,2022077470#u32,1837706654#u32,827038403#u32,1892640303#u32,370983584#u32,1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,163202459#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7619.s0
  | 1 => PV_RunJoin_ValidatorCell7619.s3
  | 2 => PV_RunJoin_ValidatorCell7619.s5
  | 3 => PV_RunJoin_ValidatorCell7619.s7
  | 4 => PV_RunJoin_ValidatorCell7619.s9
  | 5 => PV_RunJoin_ValidatorCell7619.s11
  | 6 => PV_RunJoin_ValidatorCell7619.s13
  | 7 => PV_RunJoin_ValidatorCell7619.s15
  | 8 => PV_RunJoin_ValidatorCell7619.s17
  | 9 => PV_RunJoin_ValidatorCell7619.s19
  | 10 => PV_RunJoin_ValidatorCell7619.s21
  | 11 => PV_RunJoin_ValidatorCell7619.s23
  | _ => PV_RunJoin_ValidatorCell7619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1385985564#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1312452205#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨34748210#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2022077470#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1837706654#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨827038403#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1892640303#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨370983584#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7619.s2,PV_RunJoin_ValidatorCell7619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s4,PV_RunJoin_ValidatorCell7619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s6,PV_RunJoin_ValidatorCell7619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s8,PV_RunJoin_ValidatorCell7619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s10,PV_RunJoin_ValidatorCell7619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s12,PV_RunJoin_ValidatorCell7619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s14,PV_RunJoin_ValidatorCell7619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s16,PV_RunJoin_ValidatorCell7619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s18,PV_RunJoin_ValidatorCell7619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s20,PV_RunJoin_ValidatorCell7619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7619.s22,PV_RunJoin_ValidatorCell7619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7619

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7719
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,176446941#u32,912396166#u32,1443369366#u32,2063088540#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a1 : State := Array.make 16#usize [475693174#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a2 : State := Array.make 16#usize [475693174#u32,322457381#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a3 : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a4 : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,0#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a5 : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,176446941#u32,0#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a6 : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,176446941#u32,912396166#u32,0#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a7 : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,176446941#u32,912396166#u32,1443369366#u32,0#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def a8 : State := Array.make 16#usize [475693174#u32,322457381#u32,396535705#u32,1030492646#u32,176446941#u32,912396166#u32,1443369366#u32,2063088540#u32,1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,1031854335#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7719.s0
  | 1 => PV_RunJoin_ValidatorCell7719.s3
  | 2 => PV_RunJoin_ValidatorCell7719.s5
  | 3 => PV_RunJoin_ValidatorCell7719.s7
  | 4 => PV_RunJoin_ValidatorCell7719.s9
  | 5 => PV_RunJoin_ValidatorCell7719.s11
  | 6 => PV_RunJoin_ValidatorCell7719.s13
  | 7 => PV_RunJoin_ValidatorCell7719.s15
  | 8 => PV_RunJoin_ValidatorCell7719.s17
  | 9 => PV_RunJoin_ValidatorCell7719.s19
  | 10 => PV_RunJoin_ValidatorCell7719.s21
  | 11 => PV_RunJoin_ValidatorCell7719.s23
  | _ => PV_RunJoin_ValidatorCell7719.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨475693174#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨322457381#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨396535705#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1030492646#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨176446941#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨912396166#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1443369366#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2063088540#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7719.s2,PV_RunJoin_ValidatorCell7719.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s4,PV_RunJoin_ValidatorCell7719.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s6,PV_RunJoin_ValidatorCell7719.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s8,PV_RunJoin_ValidatorCell7719.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s10,PV_RunJoin_ValidatorCell7719.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s12,PV_RunJoin_ValidatorCell7719.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s14,PV_RunJoin_ValidatorCell7719.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s16,PV_RunJoin_ValidatorCell7719.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s18,PV_RunJoin_ValidatorCell7719.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s20,PV_RunJoin_ValidatorCell7719.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7719.s22,PV_RunJoin_ValidatorCell7719.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7719

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,2109368512#u32,559795428#u32,204366681#u32,229282374#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a1 : State := Array.make 16#usize [223002281#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a2 : State := Array.make 16#usize [223002281#u32,116293184#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a3 : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a4 : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,0#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a5 : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,2109368512#u32,0#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a6 : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,2109368512#u32,559795428#u32,0#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a7 : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,2109368512#u32,559795428#u32,204366681#u32,0#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def a8 : State := Array.make 16#usize [223002281#u32,116293184#u32,1618212914#u32,1331700281#u32,2109368512#u32,559795428#u32,204366681#u32,229282374#u32,1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,248459395#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7819.s0
  | 1 => PV_RunJoin_ValidatorCell7819.s3
  | 2 => PV_RunJoin_ValidatorCell7819.s5
  | 3 => PV_RunJoin_ValidatorCell7819.s7
  | 4 => PV_RunJoin_ValidatorCell7819.s9
  | 5 => PV_RunJoin_ValidatorCell7819.s11
  | 6 => PV_RunJoin_ValidatorCell7819.s13
  | 7 => PV_RunJoin_ValidatorCell7819.s15
  | 8 => PV_RunJoin_ValidatorCell7819.s17
  | 9 => PV_RunJoin_ValidatorCell7819.s19
  | 10 => PV_RunJoin_ValidatorCell7819.s21
  | 11 => PV_RunJoin_ValidatorCell7819.s23
  | _ => PV_RunJoin_ValidatorCell7819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨223002281#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨116293184#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1618212914#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1331700281#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2109368512#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨559795428#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨204366681#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨229282374#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7819.s2,PV_RunJoin_ValidatorCell7819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s4,PV_RunJoin_ValidatorCell7819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s6,PV_RunJoin_ValidatorCell7819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s8,PV_RunJoin_ValidatorCell7819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s10,PV_RunJoin_ValidatorCell7819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s12,PV_RunJoin_ValidatorCell7819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s14,PV_RunJoin_ValidatorCell7819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s16,PV_RunJoin_ValidatorCell7819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s18,PV_RunJoin_ValidatorCell7819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s20,PV_RunJoin_ValidatorCell7819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7819.s22,PV_RunJoin_ValidatorCell7819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell7919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,531978693#u32,466210636#u32,1100375901#u32,1136408495#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a1 : State := Array.make 16#usize [204734161#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a2 : State := Array.make 16#usize [204734161#u32,1001842950#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a3 : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a4 : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,0#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a5 : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,531978693#u32,0#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a6 : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,531978693#u32,466210636#u32,0#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a7 : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,531978693#u32,466210636#u32,1100375901#u32,0#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def a8 : State := Array.make 16#usize [204734161#u32,1001842950#u32,1957867491#u32,1426920886#u32,531978693#u32,466210636#u32,1100375901#u32,1136408495#u32,1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,1546489432#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell7919.s0
  | 1 => PV_RunJoin_ValidatorCell7919.s3
  | 2 => PV_RunJoin_ValidatorCell7919.s5
  | 3 => PV_RunJoin_ValidatorCell7919.s7
  | 4 => PV_RunJoin_ValidatorCell7919.s9
  | 5 => PV_RunJoin_ValidatorCell7919.s11
  | 6 => PV_RunJoin_ValidatorCell7919.s13
  | 7 => PV_RunJoin_ValidatorCell7919.s15
  | 8 => PV_RunJoin_ValidatorCell7919.s17
  | 9 => PV_RunJoin_ValidatorCell7919.s19
  | 10 => PV_RunJoin_ValidatorCell7919.s21
  | 11 => PV_RunJoin_ValidatorCell7919.s23
  | _ => PV_RunJoin_ValidatorCell7919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨204734161#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1001842950#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1957867491#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1426920886#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨531978693#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨466210636#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1100375901#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1136408495#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell7919.s2,PV_RunJoin_ValidatorCell7919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s4,PV_RunJoin_ValidatorCell7919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s6,PV_RunJoin_ValidatorCell7919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s8,PV_RunJoin_ValidatorCell7919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s10,PV_RunJoin_ValidatorCell7919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s12,PV_RunJoin_ValidatorCell7919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s14,PV_RunJoin_ValidatorCell7919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s16,PV_RunJoin_ValidatorCell7919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s18,PV_RunJoin_ValidatorCell7919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s20,PV_RunJoin_ValidatorCell7919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell7919.s22,PV_RunJoin_ValidatorCell7919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell7919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell8019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,1817944500#u32,96708207#u32,529143660#u32,294781830#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a1 : State := Array.make 16#usize [1898472488#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a2 : State := Array.make 16#usize [1898472488#u32,597255419#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a3 : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,0#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a4 : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,0#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a5 : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,1817944500#u32,0#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a6 : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,1817944500#u32,96708207#u32,0#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a7 : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,1817944500#u32,96708207#u32,529143660#u32,0#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def a8 : State := Array.make 16#usize [1898472488#u32,597255419#u32,137386091#u32,1805069421#u32,1817944500#u32,96708207#u32,529143660#u32,294781830#u32,19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,1761530072#u32]
def absorbed (n : Nat) : State := match n with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8
  | _ => a8
def states (n : Nat) : State := match n with
  | 0 => PV_RunJoin_ValidatorCell8019.s0
  | 1 => PV_RunJoin_ValidatorCell8019.s3
  | 2 => PV_RunJoin_ValidatorCell8019.s5
  | 3 => PV_RunJoin_ValidatorCell8019.s7
  | 4 => PV_RunJoin_ValidatorCell8019.s9
  | 5 => PV_RunJoin_ValidatorCell8019.s11
  | 6 => PV_RunJoin_ValidatorCell8019.s13
  | 7 => PV_RunJoin_ValidatorCell8019.s15
  | 8 => PV_RunJoin_ValidatorCell8019.s17
  | 9 => PV_RunJoin_ValidatorCell8019.s19
  | 10 => PV_RunJoin_ValidatorCell8019.s21
  | 11 => PV_RunJoin_ValidatorCell8019.s23
  | _ => PV_RunJoin_ValidatorCell8019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1898472488#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨597255419#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨137386091#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1805069421#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1817944500#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨96708207#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨529143660#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨294781830#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell8019.s2,PV_RunJoin_ValidatorCell8019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s4,PV_RunJoin_ValidatorCell8019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s6,PV_RunJoin_ValidatorCell8019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s8,PV_RunJoin_ValidatorCell8019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s10,PV_RunJoin_ValidatorCell8019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s12,PV_RunJoin_ValidatorCell8019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s14,PV_RunJoin_ValidatorCell8019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s16,PV_RunJoin_ValidatorCell8019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s18,PV_RunJoin_ValidatorCell8019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s20,PV_RunJoin_ValidatorCell8019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell8019.s22,PV_RunJoin_ValidatorCell8019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell8019
