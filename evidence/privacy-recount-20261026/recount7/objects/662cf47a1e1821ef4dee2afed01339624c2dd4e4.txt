import R1Z.PV_RunJoin_BankCertificate19
import R1Z.PV_RunJoin_ValidatorGroup1619
import R1Z.PV_RunJoin_ValidatorGroup1919
import R1Z.PV_RunJoin_ValidatorGroup2219
import R1Z.PV_RunJoin_ValidatorGroup2519
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1819
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,1261374148#u32,1230772006#u32,1621463387#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a1 : State := Array.make 16#usize [1843107484#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a2 : State := Array.make 16#usize [1843107484#u32,377090426#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a3 : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a4 : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,0#u32,0#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a5 : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,0#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a6 : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,1261374148#u32,0#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a7 : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,1261374148#u32,1230772006#u32,0#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
def a8 : State := Array.make 16#usize [1843107484#u32,377090426#u32,1232835735#u32,1598963180#u32,1994057985#u32,1261374148#u32,1230772006#u32,1621463387#u32,2221#u32,2238#u32,2255#u32,2272#u32,2289#u32,2306#u32,2323#u32,1095964969#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1819.s0
  | 1 => PV_RunJoin_ValidatorCell1819.s3
  | 2 => PV_RunJoin_ValidatorCell1819.s5
  | 3 => PV_RunJoin_ValidatorCell1819.s7
  | 4 => PV_RunJoin_ValidatorCell1819.s9
  | 5 => PV_RunJoin_ValidatorCell1819.s11
  | 6 => PV_RunJoin_ValidatorCell1819.s13
  | 7 => PV_RunJoin_ValidatorCell1819.s15
  | 8 => PV_RunJoin_ValidatorCell1819.s17
  | 9 => PV_RunJoin_ValidatorCell1819.s19
  | 10 => PV_RunJoin_ValidatorCell1819.s21
  | 11 => PV_RunJoin_ValidatorCell1819.s23
  | _ => PV_RunJoin_ValidatorCell1819.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1843107484#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨377090426#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1232835735#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1598963180#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1994057985#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1261374148#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1230772006#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1621463387#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1819.s2,PV_RunJoin_ValidatorCell1819.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s4,PV_RunJoin_ValidatorCell1819.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s6,PV_RunJoin_ValidatorCell1819.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s8,PV_RunJoin_ValidatorCell1819.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s10,PV_RunJoin_ValidatorCell1819.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s12,PV_RunJoin_ValidatorCell1819.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s14,PV_RunJoin_ValidatorCell1819.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s16,PV_RunJoin_ValidatorCell1819.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s18,PV_RunJoin_ValidatorCell1819.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s20,PV_RunJoin_ValidatorCell1819.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1819.s22,PV_RunJoin_ValidatorCell1819.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1819

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell1919
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,1215624494#u32,880337038#u32,1016952666#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a1 : State := Array.make 16#usize [784754526#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a2 : State := Array.make 16#usize [784754526#u32,653487580#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a3 : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a4 : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,0#u32,0#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a5 : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,0#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a6 : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,1215624494#u32,0#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a7 : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,1215624494#u32,880337038#u32,0#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
def a8 : State := Array.make 16#usize [784754526#u32,653487580#u32,1331396859#u32,1248357024#u32,70404971#u32,1215624494#u32,880337038#u32,1016952666#u32,2241#u32,2258#u32,2275#u32,2292#u32,2309#u32,2326#u32,2343#u32,1095964989#u32]
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
  | 0 => PV_RunJoin_ValidatorCell1919.s0
  | 1 => PV_RunJoin_ValidatorCell1919.s3
  | 2 => PV_RunJoin_ValidatorCell1919.s5
  | 3 => PV_RunJoin_ValidatorCell1919.s7
  | 4 => PV_RunJoin_ValidatorCell1919.s9
  | 5 => PV_RunJoin_ValidatorCell1919.s11
  | 6 => PV_RunJoin_ValidatorCell1919.s13
  | 7 => PV_RunJoin_ValidatorCell1919.s15
  | 8 => PV_RunJoin_ValidatorCell1919.s17
  | 9 => PV_RunJoin_ValidatorCell1919.s19
  | 10 => PV_RunJoin_ValidatorCell1919.s21
  | 11 => PV_RunJoin_ValidatorCell1919.s23
  | _ => PV_RunJoin_ValidatorCell1919.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨784754526#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨653487580#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1331396859#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1248357024#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨70404971#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1215624494#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨880337038#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1016952666#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell1919.s2,PV_RunJoin_ValidatorCell1919.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s4,PV_RunJoin_ValidatorCell1919.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s6,PV_RunJoin_ValidatorCell1919.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s8,PV_RunJoin_ValidatorCell1919.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s10,PV_RunJoin_ValidatorCell1919.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s12,PV_RunJoin_ValidatorCell1919.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s14,PV_RunJoin_ValidatorCell1919.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s16,PV_RunJoin_ValidatorCell1919.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s18,PV_RunJoin_ValidatorCell1919.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s20,PV_RunJoin_ValidatorCell1919.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell1919.s22,PV_RunJoin_ValidatorCell1919.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell1919

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2019
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,1630516452#u32,660958964#u32,1526316434#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a1 : State := Array.make 16#usize [1675309617#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a2 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a3 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a4 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,0#u32,0#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a5 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,0#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a6 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,1630516452#u32,0#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a7 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,1630516452#u32,660958964#u32,0#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
def a8 : State := Array.make 16#usize [1675309617#u32,1189999060#u32,110604265#u32,1111112896#u32,1601727123#u32,1630516452#u32,660958964#u32,1526316434#u32,2261#u32,2278#u32,2295#u32,2312#u32,2329#u32,2346#u32,2363#u32,1095965009#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2019.s0
  | 1 => PV_RunJoin_ValidatorCell2019.s3
  | 2 => PV_RunJoin_ValidatorCell2019.s5
  | 3 => PV_RunJoin_ValidatorCell2019.s7
  | 4 => PV_RunJoin_ValidatorCell2019.s9
  | 5 => PV_RunJoin_ValidatorCell2019.s11
  | 6 => PV_RunJoin_ValidatorCell2019.s13
  | 7 => PV_RunJoin_ValidatorCell2019.s15
  | 8 => PV_RunJoin_ValidatorCell2019.s17
  | 9 => PV_RunJoin_ValidatorCell2019.s19
  | 10 => PV_RunJoin_ValidatorCell2019.s21
  | 11 => PV_RunJoin_ValidatorCell2019.s23
  | _ => PV_RunJoin_ValidatorCell2019.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1675309617#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1189999060#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨110604265#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1111112896#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1601727123#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1630516452#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨660958964#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1526316434#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2019.s2,PV_RunJoin_ValidatorCell2019.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s4,PV_RunJoin_ValidatorCell2019.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s6,PV_RunJoin_ValidatorCell2019.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s8,PV_RunJoin_ValidatorCell2019.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s10,PV_RunJoin_ValidatorCell2019.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s12,PV_RunJoin_ValidatorCell2019.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s14,PV_RunJoin_ValidatorCell2019.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s16,PV_RunJoin_ValidatorCell2019.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s18,PV_RunJoin_ValidatorCell2019.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s20,PV_RunJoin_ValidatorCell2019.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2019.s22,PV_RunJoin_ValidatorCell2019.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2019

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2119
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,2366#u32,2383#u32,2400#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a1 : State := Array.make 16#usize [2281#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a2 : State := Array.make 16#usize [2281#u32,2298#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a3 : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,0#u32,0#u32,0#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a4 : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,2332#u32,0#u32,0#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a5 : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,0#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a6 : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,2366#u32,0#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a7 : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,2366#u32,2383#u32,0#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
def a8 : State := Array.make 16#usize [2281#u32,2298#u32,2315#u32,2332#u32,2349#u32,2366#u32,2383#u32,2400#u32,493855764#u32,1737005017#u32,1044011334#u32,780794261#u32,292608247#u32,1805935865#u32,972083531#u32,1442600183#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2119.s0
  | 1 => PV_RunJoin_ValidatorCell2119.s3
  | 2 => PV_RunJoin_ValidatorCell2119.s5
  | 3 => PV_RunJoin_ValidatorCell2119.s7
  | 4 => PV_RunJoin_ValidatorCell2119.s9
  | 5 => PV_RunJoin_ValidatorCell2119.s11
  | 6 => PV_RunJoin_ValidatorCell2119.s13
  | 7 => PV_RunJoin_ValidatorCell2119.s15
  | 8 => PV_RunJoin_ValidatorCell2119.s17
  | 9 => PV_RunJoin_ValidatorCell2119.s19
  | 10 => PV_RunJoin_ValidatorCell2119.s21
  | 11 => PV_RunJoin_ValidatorCell2119.s23
  | _ => PV_RunJoin_ValidatorCell2119.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2281#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2298#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2315#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2332#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2349#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2366#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2383#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2400#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2119.s2,PV_RunJoin_ValidatorCell2119.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s4,PV_RunJoin_ValidatorCell2119.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s6,PV_RunJoin_ValidatorCell2119.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s8,PV_RunJoin_ValidatorCell2119.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s10,PV_RunJoin_ValidatorCell2119.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s12,PV_RunJoin_ValidatorCell2119.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s14,PV_RunJoin_ValidatorCell2119.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s16,PV_RunJoin_ValidatorCell2119.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s18,PV_RunJoin_ValidatorCell2119.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s20,PV_RunJoin_ValidatorCell2119.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2119.s22,PV_RunJoin_ValidatorCell2119.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2119

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2219
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,839141147#u32,732445005#u32,1267400728#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a1 : State := Array.make 16#usize [516145591#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a2 : State := Array.make 16#usize [516145591#u32,463254876#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a3 : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a4 : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,0#u32,0#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a5 : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,0#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a6 : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,839141147#u32,0#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a7 : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,839141147#u32,732445005#u32,0#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
def a8 : State := Array.make 16#usize [516145591#u32,463254876#u32,1878652377#u32,174797573#u32,1017414220#u32,839141147#u32,732445005#u32,1267400728#u32,2301#u32,2318#u32,2335#u32,2352#u32,2369#u32,2386#u32,2403#u32,1095965049#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2219.s0
  | 1 => PV_RunJoin_ValidatorCell2219.s3
  | 2 => PV_RunJoin_ValidatorCell2219.s5
  | 3 => PV_RunJoin_ValidatorCell2219.s7
  | 4 => PV_RunJoin_ValidatorCell2219.s9
  | 5 => PV_RunJoin_ValidatorCell2219.s11
  | 6 => PV_RunJoin_ValidatorCell2219.s13
  | 7 => PV_RunJoin_ValidatorCell2219.s15
  | 8 => PV_RunJoin_ValidatorCell2219.s17
  | 9 => PV_RunJoin_ValidatorCell2219.s19
  | 10 => PV_RunJoin_ValidatorCell2219.s21
  | 11 => PV_RunJoin_ValidatorCell2219.s23
  | _ => PV_RunJoin_ValidatorCell2219.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨516145591#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨463254876#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1878652377#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨174797573#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1017414220#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨839141147#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨732445005#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1267400728#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2219.s2,PV_RunJoin_ValidatorCell2219.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s4,PV_RunJoin_ValidatorCell2219.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s6,PV_RunJoin_ValidatorCell2219.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s8,PV_RunJoin_ValidatorCell2219.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s10,PV_RunJoin_ValidatorCell2219.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s12,PV_RunJoin_ValidatorCell2219.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s14,PV_RunJoin_ValidatorCell2219.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s16,PV_RunJoin_ValidatorCell2219.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s18,PV_RunJoin_ValidatorCell2219.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s20,PV_RunJoin_ValidatorCell2219.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2219.s22,PV_RunJoin_ValidatorCell2219.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2219

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2319
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,2406#u32,2423#u32,2440#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a1 : State := Array.make 16#usize [2321#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a2 : State := Array.make 16#usize [2321#u32,2338#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a3 : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,0#u32,0#u32,0#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a4 : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,2372#u32,0#u32,0#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a5 : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,0#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a6 : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,2406#u32,0#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a7 : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,2406#u32,2423#u32,0#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
def a8 : State := Array.make 16#usize [2321#u32,2338#u32,2355#u32,2372#u32,2389#u32,2406#u32,2423#u32,2440#u32,1275343547#u32,688077093#u32,1851184479#u32,402597576#u32,2135776699#u32,632730450#u32,2036489921#u32,40881166#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2319.s0
  | 1 => PV_RunJoin_ValidatorCell2319.s3
  | 2 => PV_RunJoin_ValidatorCell2319.s5
  | 3 => PV_RunJoin_ValidatorCell2319.s7
  | 4 => PV_RunJoin_ValidatorCell2319.s9
  | 5 => PV_RunJoin_ValidatorCell2319.s11
  | 6 => PV_RunJoin_ValidatorCell2319.s13
  | 7 => PV_RunJoin_ValidatorCell2319.s15
  | 8 => PV_RunJoin_ValidatorCell2319.s17
  | 9 => PV_RunJoin_ValidatorCell2319.s19
  | 10 => PV_RunJoin_ValidatorCell2319.s21
  | 11 => PV_RunJoin_ValidatorCell2319.s23
  | _ => PV_RunJoin_ValidatorCell2319.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2321#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2338#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2355#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2372#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2389#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2406#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2423#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2440#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2319.s2,PV_RunJoin_ValidatorCell2319.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s4,PV_RunJoin_ValidatorCell2319.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s6,PV_RunJoin_ValidatorCell2319.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s8,PV_RunJoin_ValidatorCell2319.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s10,PV_RunJoin_ValidatorCell2319.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s12,PV_RunJoin_ValidatorCell2319.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s14,PV_RunJoin_ValidatorCell2319.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s16,PV_RunJoin_ValidatorCell2319.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s18,PV_RunJoin_ValidatorCell2319.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s20,PV_RunJoin_ValidatorCell2319.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2319.s22,PV_RunJoin_ValidatorCell2319.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2319

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2419
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,1020968422#u32,1342497638#u32,1907691591#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a1 : State := Array.make 16#usize [2136837586#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a2 : State := Array.make 16#usize [2136837586#u32,679543585#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a3 : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a4 : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,0#u32,0#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a5 : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,0#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a6 : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,1020968422#u32,0#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a7 : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,1020968422#u32,1342497638#u32,0#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
def a8 : State := Array.make 16#usize [2136837586#u32,679543585#u32,225002526#u32,1101048270#u32,2134488188#u32,1020968422#u32,1342497638#u32,1907691591#u32,2341#u32,2358#u32,2375#u32,2392#u32,2409#u32,2426#u32,2443#u32,1095965089#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2419.s0
  | 1 => PV_RunJoin_ValidatorCell2419.s3
  | 2 => PV_RunJoin_ValidatorCell2419.s5
  | 3 => PV_RunJoin_ValidatorCell2419.s7
  | 4 => PV_RunJoin_ValidatorCell2419.s9
  | 5 => PV_RunJoin_ValidatorCell2419.s11
  | 6 => PV_RunJoin_ValidatorCell2419.s13
  | 7 => PV_RunJoin_ValidatorCell2419.s15
  | 8 => PV_RunJoin_ValidatorCell2419.s17
  | 9 => PV_RunJoin_ValidatorCell2419.s19
  | 10 => PV_RunJoin_ValidatorCell2419.s21
  | 11 => PV_RunJoin_ValidatorCell2419.s23
  | _ => PV_RunJoin_ValidatorCell2419.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2136837586#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨679543585#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨225002526#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1101048270#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2134488188#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1020968422#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1342497638#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1907691591#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2419.s2,PV_RunJoin_ValidatorCell2419.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s4,PV_RunJoin_ValidatorCell2419.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s6,PV_RunJoin_ValidatorCell2419.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s8,PV_RunJoin_ValidatorCell2419.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s10,PV_RunJoin_ValidatorCell2419.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s12,PV_RunJoin_ValidatorCell2419.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s14,PV_RunJoin_ValidatorCell2419.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s16,PV_RunJoin_ValidatorCell2419.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s18,PV_RunJoin_ValidatorCell2419.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s20,PV_RunJoin_ValidatorCell2419.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2419.s22,PV_RunJoin_ValidatorCell2419.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2419

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2519
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,2446#u32,2463#u32,2480#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a1 : State := Array.make 16#usize [2361#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a2 : State := Array.make 16#usize [2361#u32,2378#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a3 : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a4 : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,2412#u32,0#u32,0#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a5 : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,0#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a6 : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,2446#u32,0#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a7 : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,2446#u32,2463#u32,0#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
def a8 : State := Array.make 16#usize [2361#u32,2378#u32,2395#u32,2412#u32,2429#u32,2446#u32,2463#u32,2480#u32,2081739590#u32,582598927#u32,447833412#u32,1551242300#u32,10472096#u32,1276966930#u32,111682118#u32,1228302511#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2519.s0
  | 1 => PV_RunJoin_ValidatorCell2519.s3
  | 2 => PV_RunJoin_ValidatorCell2519.s5
  | 3 => PV_RunJoin_ValidatorCell2519.s7
  | 4 => PV_RunJoin_ValidatorCell2519.s9
  | 5 => PV_RunJoin_ValidatorCell2519.s11
  | 6 => PV_RunJoin_ValidatorCell2519.s13
  | 7 => PV_RunJoin_ValidatorCell2519.s15
  | 8 => PV_RunJoin_ValidatorCell2519.s17
  | 9 => PV_RunJoin_ValidatorCell2519.s19
  | 10 => PV_RunJoin_ValidatorCell2519.s21
  | 11 => PV_RunJoin_ValidatorCell2519.s23
  | _ => PV_RunJoin_ValidatorCell2519.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨2361#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2378#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2395#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2412#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2429#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2446#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2463#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨2480#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2519.s2,PV_RunJoin_ValidatorCell2519.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s4,PV_RunJoin_ValidatorCell2519.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s6,PV_RunJoin_ValidatorCell2519.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s8,PV_RunJoin_ValidatorCell2519.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s10,PV_RunJoin_ValidatorCell2519.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s12,PV_RunJoin_ValidatorCell2519.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s14,PV_RunJoin_ValidatorCell2519.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s16,PV_RunJoin_ValidatorCell2519.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s18,PV_RunJoin_ValidatorCell2519.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s20,PV_RunJoin_ValidatorCell2519.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2519.s22,PV_RunJoin_ValidatorCell2519.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2519

set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCell2619
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_BankCertificate19
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def absorption : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,1723220283#u32,85709078#u32,537745032#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32]
def a0 : State := Array.make 16#usize [0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a1 : State := Array.make 16#usize [1272212618#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a2 : State := Array.make 16#usize [1272212618#u32,615811090#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a3 : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,0#u32,0#u32,0#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a4 : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,0#u32,0#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a5 : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,0#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a6 : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,1723220283#u32,0#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a7 : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,1723220283#u32,85709078#u32,0#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
def a8 : State := Array.make 16#usize [1272212618#u32,615811090#u32,570892109#u32,1073257360#u32,1217412274#u32,1723220283#u32,85709078#u32,537745032#u32,2381#u32,2398#u32,2415#u32,2432#u32,2449#u32,2466#u32,2483#u32,1095965129#u32]
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
  | 0 => PV_RunJoin_ValidatorCell2619.s0
  | 1 => PV_RunJoin_ValidatorCell2619.s3
  | 2 => PV_RunJoin_ValidatorCell2619.s5
  | 3 => PV_RunJoin_ValidatorCell2619.s7
  | 4 => PV_RunJoin_ValidatorCell2619.s9
  | 5 => PV_RunJoin_ValidatorCell2619.s11
  | 6 => PV_RunJoin_ValidatorCell2619.s13
  | 7 => PV_RunJoin_ValidatorCell2619.s15
  | 8 => PV_RunJoin_ValidatorCell2619.s17
  | 9 => PV_RunJoin_ValidatorCell2619.s19
  | 10 => PV_RunJoin_ValidatorCell2619.s21
  | 11 => PV_RunJoin_ValidatorCell2619.s23
  | _ => PV_RunJoin_ValidatorCell2619.s0
theorem add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1) := by
  intro lane
  fin_cases lane
  · exact ⟨1272212618#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨615811090#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨570892109#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1073257360#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1217412274#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨1723220283#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨85709078#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
  · exact ⟨537745032#u32,by with_unfolding_all rfl,by with_unfolding_all rfl⟩
#print axioms add
theorem pairs : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1))) := by
  intro n
  fin_cases n
  · exact ⟨PV_RunJoin_ValidatorCell2619.s2,PV_RunJoin_ValidatorCell2619.pair0⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s4,PV_RunJoin_ValidatorCell2619.pair1⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s6,PV_RunJoin_ValidatorCell2619.pair2⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s8,PV_RunJoin_ValidatorCell2619.pair3⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s10,PV_RunJoin_ValidatorCell2619.pair4⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s12,PV_RunJoin_ValidatorCell2619.pair5⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s14,PV_RunJoin_ValidatorCell2619.pair6⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s16,PV_RunJoin_ValidatorCell2619.pair7⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s18,PV_RunJoin_ValidatorCell2619.pair8⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s20,PV_RunJoin_ValidatorCell2619.pair9⟩
  · exact ⟨PV_RunJoin_ValidatorCell2619.s22,PV_RunJoin_ValidatorCell2619.pair10⟩
#print axioms pairs
def certificate : Certificate := {
  pre := a0, absorption := absorption, absorbed := absorbed, states := states,
  before := rfl, after := by with_unfolding_all rfl, add := add, pair := pairs }
end R1Z.PV_RunJoin_BankCell2619
