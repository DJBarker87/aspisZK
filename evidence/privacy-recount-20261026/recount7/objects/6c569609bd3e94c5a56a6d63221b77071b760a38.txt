import R1Z.PV_RunJoin_SquareChain20
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InverseChain20
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort
theorem mul0 : aspis_core.field.M31.mul 351017421#u32 351017421#u32 = ok 536684984#u32 := by
  with_unfolding_all rfl
#print axioms mul0
theorem mul1 : aspis_core.field.M31.mul 536684984#u32 351017421#u32 = ok 833089556#u32 := by
  with_unfolding_all rfl
#print axioms mul1
theorem mul2 : aspis_core.field.M31.mul 833089556#u32 833089556#u32 = ok 1451291061#u32 := by
  with_unfolding_all rfl
#print axioms mul2
theorem mul3 : aspis_core.field.M31.mul 1451291061#u32 1451291061#u32 = ok 1873547433#u32 := by
  with_unfolding_all rfl
#print axioms mul3
def states2 (n : Nat) : U32 := match n with
  | 0 => 833089556#u32
  | 1 => 1451291061#u32
  | 2 => 1873547433#u32
  | _ => 1873547433#u32
theorem square2 : aspis_core.field.square_n 833089556#u32 2#usize = ok 1873547433#u32 := by
  have hf : ∀ i, i < 2 → aspis_core.field.M31.mul (states2 i) (states2 i) = ok (states2 (i+1)) := by
    intro i hi
    interval_cases i
    · exact mul2
    · exact mul3
  exact PV_RunJoin_SquareChain20.source states2 2#usize hf
#print axioms square2
theorem mul4 : aspis_core.field.M31.mul 1873547433#u32 833089556#u32 = ok 1805721478#u32 := by
  with_unfolding_all rfl
#print axioms mul4
theorem mul5 : aspis_core.field.M31.mul 1805721478#u32 1805721478#u32 = ok 149808554#u32 := by
  with_unfolding_all rfl
#print axioms mul5
theorem mul6 : aspis_core.field.M31.mul 149808554#u32 149808554#u32 = ok 728566719#u32 := by
  with_unfolding_all rfl
#print axioms mul6
theorem mul7 : aspis_core.field.M31.mul 728566719#u32 728566719#u32 = ok 971741515#u32 := by
  with_unfolding_all rfl
#print axioms mul7
theorem mul8 : aspis_core.field.M31.mul 971741515#u32 971741515#u32 = ok 1269973541#u32 := by
  with_unfolding_all rfl
#print axioms mul8
def states4 (n : Nat) : U32 := match n with
  | 0 => 1805721478#u32
  | 1 => 149808554#u32
  | 2 => 728566719#u32
  | 3 => 971741515#u32
  | 4 => 1269973541#u32
  | _ => 1269973541#u32
theorem square4 : aspis_core.field.square_n 1805721478#u32 4#usize = ok 1269973541#u32 := by
  have hf : ∀ i, i < 4 → aspis_core.field.M31.mul (states4 i) (states4 i) = ok (states4 (i+1)) := by
    intro i hi
    interval_cases i
    · exact mul5
    · exact mul6
    · exact mul7
    · exact mul8
  exact PV_RunJoin_SquareChain20.source states4 4#usize hf
#print axioms square4
theorem mul9 : aspis_core.field.M31.mul 1269973541#u32 1805721478#u32 = ok 87844485#u32 := by
  with_unfolding_all rfl
#print axioms mul9
theorem mul10 : aspis_core.field.M31.mul 87844485#u32 87844485#u32 = ok 1771902363#u32 := by
  with_unfolding_all rfl
#print axioms mul10
theorem mul11 : aspis_core.field.M31.mul 1771902363#u32 1771902363#u32 = ok 2132100114#u32 := by
  with_unfolding_all rfl
#print axioms mul11
theorem mul12 : aspis_core.field.M31.mul 2132100114#u32 2132100114#u32 = ok 389662689#u32 := by
  with_unfolding_all rfl
#print axioms mul12
theorem mul13 : aspis_core.field.M31.mul 389662689#u32 389662689#u32 = ok 276328875#u32 := by
  with_unfolding_all rfl
#print axioms mul13
theorem mul14 : aspis_core.field.M31.mul 276328875#u32 276328875#u32 = ok 619116025#u32 := by
  with_unfolding_all rfl
#print axioms mul14
theorem mul15 : aspis_core.field.M31.mul 619116025#u32 619116025#u32 = ok 2053510986#u32 := by
  with_unfolding_all rfl
#print axioms mul15
theorem mul16 : aspis_core.field.M31.mul 2053510986#u32 2053510986#u32 = ok 237063991#u32 := by
  with_unfolding_all rfl
#print axioms mul16
theorem mul17 : aspis_core.field.M31.mul 237063991#u32 237063991#u32 = ok 171986896#u32 := by
  with_unfolding_all rfl
#print axioms mul17
def states8 (n : Nat) : U32 := match n with
  | 0 => 87844485#u32
  | 1 => 1771902363#u32
  | 2 => 2132100114#u32
  | 3 => 389662689#u32
  | 4 => 276328875#u32
  | 5 => 619116025#u32
  | 6 => 2053510986#u32
  | 7 => 237063991#u32
  | 8 => 171986896#u32
  | _ => 171986896#u32
theorem square8 : aspis_core.field.square_n 87844485#u32 8#usize = ok 171986896#u32 := by
  have hf : ∀ i, i < 8 → aspis_core.field.M31.mul (states8 i) (states8 i) = ok (states8 (i+1)) := by
    intro i hi
    interval_cases i
    · exact mul10
    · exact mul11
    · exact mul12
    · exact mul13
    · exact mul14
    · exact mul15
    · exact mul16
    · exact mul17
  exact PV_RunJoin_SquareChain20.source states8 8#usize hf
#print axioms square8
theorem mul18 : aspis_core.field.M31.mul 171986896#u32 87844485#u32 = ok 945926281#u32 := by
  with_unfolding_all rfl
#print axioms mul18
theorem mul19 : aspis_core.field.M31.mul 945926281#u32 945926281#u32 = ok 1248095831#u32 := by
  with_unfolding_all rfl
#print axioms mul19
theorem mul20 : aspis_core.field.M31.mul 1248095831#u32 1248095831#u32 = ok 1522749426#u32 := by
  with_unfolding_all rfl
#print axioms mul20
theorem mul21 : aspis_core.field.M31.mul 1522749426#u32 1522749426#u32 = ok 1275007798#u32 := by
  with_unfolding_all rfl
#print axioms mul21
theorem mul22 : aspis_core.field.M31.mul 1275007798#u32 1275007798#u32 = ok 405009974#u32 := by
  with_unfolding_all rfl
#print axioms mul22
theorem mul23 : aspis_core.field.M31.mul 405009974#u32 405009974#u32 = ok 1679645138#u32 := by
  with_unfolding_all rfl
#print axioms mul23
theorem mul24 : aspis_core.field.M31.mul 1679645138#u32 1679645138#u32 = ok 1466274647#u32 := by
  with_unfolding_all rfl
#print axioms mul24
theorem mul25 : aspis_core.field.M31.mul 1466274647#u32 1466274647#u32 = ok 1964993654#u32 := by
  with_unfolding_all rfl
#print axioms mul25
theorem mul26 : aspis_core.field.M31.mul 1964993654#u32 1964993654#u32 = ok 968048739#u32 := by
  with_unfolding_all rfl
#print axioms mul26
def states16 (n : Nat) : U32 := match n with
  | 0 => 945926281#u32
  | 1 => 1248095831#u32
  | 2 => 1522749426#u32
  | 3 => 1275007798#u32
  | 4 => 405009974#u32
  | 5 => 1679645138#u32
  | 6 => 1466274647#u32
  | 7 => 1964993654#u32
  | 8 => 968048739#u32
  | _ => 968048739#u32
theorem square16 : aspis_core.field.square_n 945926281#u32 8#usize = ok 968048739#u32 := by
  have hf : ∀ i, i < 8 → aspis_core.field.M31.mul (states16 i) (states16 i) = ok (states16 (i+1)) := by
    intro i hi
    interval_cases i
    · exact mul19
    · exact mul20
    · exact mul21
    · exact mul22
    · exact mul23
    · exact mul24
    · exact mul25
    · exact mul26
  exact PV_RunJoin_SquareChain20.source states16 8#usize hf
#print axioms square16
theorem mul27 : aspis_core.field.M31.mul 968048739#u32 87844485#u32 = ok 1851269167#u32 := by
  with_unfolding_all rfl
#print axioms mul27
theorem mul28 : aspis_core.field.M31.mul 1851269167#u32 1851269167#u32 = ok 1736146078#u32 := by
  with_unfolding_all rfl
#print axioms mul28
theorem mul29 : aspis_core.field.M31.mul 1736146078#u32 1736146078#u32 = ok 1948689716#u32 := by
  with_unfolding_all rfl
#print axioms mul29
theorem mul30 : aspis_core.field.M31.mul 1948689716#u32 1948689716#u32 = ok 2138188201#u32 := by
  with_unfolding_all rfl
#print axioms mul30
theorem mul31 : aspis_core.field.M31.mul 2138188201#u32 2138188201#u32 = ok 1311801871#u32 := by
  with_unfolding_all rfl
#print axioms mul31
def states24 (n : Nat) : U32 := match n with
  | 0 => 1851269167#u32
  | 1 => 1736146078#u32
  | 2 => 1948689716#u32
  | 3 => 2138188201#u32
  | 4 => 1311801871#u32
  | _ => 1311801871#u32
theorem square24 : aspis_core.field.square_n 1851269167#u32 4#usize = ok 1311801871#u32 := by
  have hf : ∀ i, i < 4 → aspis_core.field.M31.mul (states24 i) (states24 i) = ok (states24 (i+1)) := by
    intro i hi
    interval_cases i
    · exact mul28
    · exact mul29
    · exact mul30
    · exact mul31
  exact PV_RunJoin_SquareChain20.source states24 4#usize hf
#print axioms square24
theorem mul32 : aspis_core.field.M31.mul 1311801871#u32 1805721478#u32 = ok 525458904#u32 := by
  with_unfolding_all rfl
#print axioms mul32
theorem mul33 : aspis_core.field.M31.mul 525458904#u32 525458904#u32 = ok 2056815120#u32 := by
  with_unfolding_all rfl
#print axioms mul33
theorem mul34 : aspis_core.field.M31.mul 2056815120#u32 351017421#u32 = ok 1268624648#u32 := by
  with_unfolding_all rfl
#print axioms mul34
theorem mul35 : aspis_core.field.M31.mul 1268624648#u32 1268624648#u32 = ok 225401153#u32 := by
  with_unfolding_all rfl
#print axioms mul35
theorem mul36 : aspis_core.field.M31.mul 225401153#u32 225401153#u32 = ok 551895423#u32 := by
  with_unfolding_all rfl
#print axioms mul36
theorem mul37 : aspis_core.field.M31.mul 551895423#u32 351017421#u32 = ok 225401153#u32 := by
  with_unfolding_all rfl
#print axioms mul37
theorem inverse : aspis_core.field.M31.inv 351017421#u32 = ok 225401153#u32 := by
  rw [aspis_core.field.M31.inv]
  simp only [show ((351017421#u32 : U32) != 0#u32) = true from rfl,massert,if_true,bind_tc_ok]
  rw [mul0]
  simp only [bind_tc_ok]
  rw [mul1]
  simp only [bind_tc_ok]
  rw [square2]
  simp only [bind_tc_ok]
  rw [mul4]
  simp only [bind_tc_ok]
  rw [square4]
  simp only [bind_tc_ok]
  rw [mul9]
  simp only [bind_tc_ok]
  rw [square8]
  simp only [bind_tc_ok]
  rw [mul18]
  simp only [bind_tc_ok]
  rw [square16]
  simp only [bind_tc_ok]
  rw [mul27]
  simp only [bind_tc_ok]
  rw [square24]
  simp only [bind_tc_ok]
  rw [mul32]
  simp only [bind_tc_ok]
  rw [mul33]
  simp only [bind_tc_ok]
  rw [mul34]
  simp only [bind_tc_ok]
  rw [mul35]
  simp only [bind_tc_ok]
  rw [mul36]
  simp only [bind_tc_ok]
  rw [mul37]
#print axioms inverse
theorem product : aspis_core.field.M31.mul 351017421#u32 225401153#u32 = ok 1#u32 := by
  with_unfolding_all rfl
#print axioms product
end R1Z.PV_RunJoin_InverseChain20
