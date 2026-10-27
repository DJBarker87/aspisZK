import XRo_Join_Carriers
import XRn_Join_Funs
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XRr_SemanticCarriers
abbrev CP := AspisR1PublicPreparation.r1_wire.Prefix
abbrev CV := AspisR1PublicPreparation.r1_wire.ValidatedRecord
abbrev CW := AspisR1PublicPreparation.r1_wire.Error
def prefix (p : r1_wire.Prefix) : CP := ⟨p.c1_root,p.records⟩
def emitted (p : CP) : r1_wire.Prefix := ⟨p.c1_root,p.records⟩
def record (v : r1_wire.ValidatedRecord) : CV := ⟨v.row,v.framed⟩
def emittedRecord (v : CV) : r1_wire.ValidatedRecord := ⟨v.row,v.framed⟩
def wire : r1_wire.Error → CW
 | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
 | .InvalidRow => .InvalidRow | .Tag a => .Tag a | .Length a => .Length a
 | .NonCanonical a b => .NonCanonical a b | .Boundary a => .Boundary a
 | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes | .Public => .Public
def emittedWire : CW → r1_wire.Error
 | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
 | .InvalidRow => .InvalidRow | .Tag a => .Tag a | .Length a => .Length a
 | .NonCanonical a b => .NonCanonical a b | .Boundary a => .Boundary a
 | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
 | .TrailingBytes => .TrailingBytes | .Public => .Public
theorem prefix_round (p : CP) : prefix (emitted p)=p := by cases p;rfl
theorem emitted_round (p : r1_wire.Prefix) : emitted (prefix p)=p := by cases p;rfl
theorem record_round (v : CV) : record (emittedRecord v)=v := by cases v;rfl
theorem emittedRecord_round (v : r1_wire.ValidatedRecord) : emittedRecord (record v)=v := by cases v;rfl
theorem wire_round (e : CW) : wire (emittedWire e)=e := by cases e <;> rfl
theorem emittedWire_round (e : r1_wire.Error) : emittedWire (wire e)=e := by cases e <;> rfl
#print axioms prefix_round
#print axioms emitted_round
#print axioms record_round
#print axioms emittedRecord_round
#print axioms wire_round
#print axioms emittedWire_round
end XRr_SemanticCarriers
