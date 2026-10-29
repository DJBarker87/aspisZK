import PV_B3P_CompositionSuccess8227
import PV_B3P_P227_14
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] valid_public reference_terminal.composition_parts
  reference_terminal.equality_value aspis_core.field.QM31.mul aspis_core.field.QM31.add
  aspis_core.field.QM31.sub reference_terminal.select227

theorem terminal_parts_success8 (p : reference_terminal.SemanticPublic)
    (claims : Array aspis_core.field.QM31 84#usize)
    (point zc : Array aspis_core.field.QM31 10#usize)
    (lambda chi theta mu : aspis_core.field.QM31) :
    RustOk (reference_terminal.terminal_parts (valid_public p) claims point lambda chi theta zc mu) := by
  obtain ⟨parts,hparts⟩ := composition_success8 p claims point lambda chi theta
  unfold reference_terminal.terminal_parts
  rw [hparts]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rcases parts with ⟨composition,c1,mask,g,h1,active⟩
  apply rust_bind
  · exact total_reference_terminal_equality_value zc point
  intro equality
  apply rust_bind
  · exact qmul equality composition
  intro q1
  apply rust_bind
  · exact qmul mu h1
  intro q2
  apply rust_bind
  · exact qadd q1 q2
  intro q3
  apply rust_bind
  · exact qmul mu mu
  intro q4
  apply rust_bind
  · exact qsub _ active
  intro q5
  apply rust_bind
  · exact qmul q5 h1
  intro q6
  apply rust_bind
  · exact qmul q4 q6
  intro q7
  apply rust_bind
  · exact qadd q3 q7
  intro original
  exact rust_ok _

attribute [local irreducible] reference_terminal.terminal_parts

theorem reference_success8 (p : reference_terminal.SemanticPublic)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :
    RustOk (reference_terminal.reference227 (valid_public p) claims point c) := by
  obtain ⟨selected,hselected,_⟩ := PV_B3P_SelectValue227.nonvacuity claims
  obtain ⟨parts,hparts⟩ := terminal_parts_success8 p selected point c.zc c.lambda c.chi c.theta c.mu
  unfold reference_terminal.reference227
  rw [hselected]
  change RustOk (reference_terminal.terminal_parts (valid_public p) selected point
    c.lambda c.chi c.theta c.zc c.mu >>= _)
  rw [hparts]
  rcases parts with ⟨value,c1,mask,g⟩
  exact rust_ok value

#print axioms terminal_parts_success8
#print axioms reference_success8
end PV_B3P_Success227
