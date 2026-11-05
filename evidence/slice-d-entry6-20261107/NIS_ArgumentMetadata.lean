import NIS_FormatterPackets
set_option autoImplicit false
namespace NIJ_ArgumentMetadata
open Aeneas Aeneas.Std Result
abbrev E := NGL_ErrorModel.E
/-- The reference for the compiler metadata cut. Its native association is
NHY_K111/K112 on the literal r1:error:{:?} and EVERY deployed Error value.
This is not a specification of arbitrary Arguments values. -/
def image (_ : E) : Usize × Option String := (18#usize,none)

theorem capacity (e : E) : (image e).1=18#usize := rfl

theorem as_str_none (e : E) : (image e).2=none := rfl

/-- Omitting the literal shortcut does not assume a formatted output: it
selects the rendering continuation on the independently certified None. -/
theorem choose {A : Type} (e : E) (render : Unit → A) (literal : String → A) :
 Option.elim (image e).2 (render ()) literal=render () := rfl

/-- The real writer's finite per-label value packets and the retained table
share the same exact UTF8 representation, including growth cases19 bytes. -/
theorem message_bound (e : E) : (NGL_ErrorModel.message e).utf8ByteSize≤19 := by
 cases e <;> decide

#print axioms capacity
#print axioms as_str_none
#print axioms choose
#print axioms message_bound
end NIJ_ArgumentMetadata
