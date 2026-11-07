import NNG_TypedDomains136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckedCalls136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_TypedDomains136

theorem terminal {Reply : Type} (args : Public × Claims × Alpha × aspis_core.state_only_prefix.r0.Challenges) (r : Result Reply) (domain : terminal args) :
    Checked (.call "terminal" args r) := by
  constructor
  · exact (same "terminal" terminal args r).mpr domain
  · exact NNG_TypedDomains136.other "mask" "terminal" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "terminal" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "terminal" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "terminal" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "terminal" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "terminal" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "terminal" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "terminal" decode args r (by decide)
#print axioms terminal

theorem mask {Reply : Type} (args : Array Q 16#usize × Alpha × Q × Alpha) (r : Result Reply) (domain : mask args) :
    Checked (.call "mask" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mask" terminal args r (by decide)
  · exact (same "mask" mask args r).mpr domain
  · exact NNG_TypedDomains136.other "multiply" "mask" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mask" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mask" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mask" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mask" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mask" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mask" decode args r (by decide)
#print axioms mask

theorem multiply {Reply : Type} (args : Q × Q) (r : Result Reply) (domain : arithmetic args) :
    Checked (.call "multiply" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "multiply" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "multiply" mask args r (by decide)
  · exact (same "multiply" arithmetic args r).mpr domain
  · exact NNG_TypedDomains136.other "addMask" "multiply" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "multiply" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "multiply" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "multiply" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "multiply" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "multiply" decode args r (by decide)
#print axioms multiply

theorem addMask {Reply : Type} (args : Q × Q) (r : Result Reply) (domain : arithmetic args) :
    Checked (.call "addMask" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "addMask" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "addMask" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "addMask" arithmetic args r (by decide)
  · exact (same "addMask" arithmetic args r).mpr domain
  · exact NNG_TypedDomains136.other "addExtra" "addMask" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "addMask" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "addMask" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "addMask" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "addMask" decode args r (by decide)
#print axioms addMask

theorem addExtra {Reply : Type} (args : Q × Q) (r : Result Reply) (domain : arithmetic args) :
    Checked (.call "addExtra" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "addExtra" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "addExtra" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "addExtra" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "addExtra" arithmetic args r (by decide)
  · exact (same "addExtra" arithmetic args r).mpr domain
  · exact NNG_TypedDomains136.other "circle0" "addExtra" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "addExtra" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "addExtra" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "addExtra" decode args r (by decide)
#print axioms addExtra

theorem circle0 {Reply : Type} (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) (r : Result Reply) (domain : circle args) :
    Checked (.call "circle0" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "circle0" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "circle0" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "circle0" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "circle0" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "circle0" arithmetic args r (by decide)
  · exact (same "circle0" circle args r).mpr domain
  · exact NNG_TypedDomains136.other "circle1" "circle0" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "circle0" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "circle0" decode args r (by decide)
#print axioms circle0

theorem circle1 {Reply : Type} (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) (r : Result Reply) (domain : circle args) :
    Checked (.call "circle1" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "circle1" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "circle1" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "circle1" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "circle1" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "circle1" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "circle1" circle args r (by decide)
  · exact (same "circle1" circle args r).mpr domain
  · exact NNG_TypedDomains136.other "extra" "circle1" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "circle1" decode args r (by decide)
#print axioms circle1

theorem extra {Reply : Type} (args : r1_wire.ValidatedRecord × Usize) (r : Result Reply) (domain : decode args) :
    Checked (.call "extra" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "extra" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "extra" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "extra" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "extra" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "extra" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "extra" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "extra" circle args r (by decide)
  · exact (same "extra" decode args r).mpr domain
  · exact NNG_TypedDomains136.other "beforeZ1" "extra" decode args r (by decide)
#print axioms extra

theorem beforeZ1 {Reply : Type} (args : r1_wire.ValidatedRecord × Usize) (r : Result Reply) (domain : decode args) :
    Checked (.call "beforeZ1" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "beforeZ1" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "beforeZ1" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "beforeZ1" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "beforeZ1" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "beforeZ1" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "beforeZ1" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "beforeZ1" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "beforeZ1" decode args r (by decide)
  · exact (same "beforeZ1" decode args r).mpr domain
#print axioms beforeZ1

theorem rounds {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "rounds" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "rounds" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "rounds" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "rounds" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "rounds" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "rounds" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "rounds" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "rounds" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "rounds" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "rounds" decode args r (by decide)
#print axioms rounds

theorem claims {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "claims" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "claims" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "claims" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "claims" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "claims" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "claims" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "claims" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "claims" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "claims" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "claims" decode args r (by decide)
#print axioms claims

theorem record25 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "record25" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "record25" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "record25" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "record25" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "record25" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "record25" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "record25" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "record25" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "record25" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "record25" decode args r (by decide)
#print axioms record25

theorem record26 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "record26" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "record26" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "record26" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "record26" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "record26" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "record26" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "record26" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "record26" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "record26" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "record26" decode args r (by decide)
#print axioms record26

theorem state {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "state" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "state" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "state" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "state" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "state" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "state" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "state" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "state" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "state" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "state" decode args r (by decide)
#print axioms state

theorem payload2 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "payload2" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "payload2" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "payload2" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "payload2" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "payload2" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "payload2" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "payload2" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "payload2" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "payload2" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "payload2" decode args r (by decide)
#print axioms payload2

theorem mark2 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark2" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark2" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark2" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark2" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark2" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark2" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark2" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark2" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark2" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark2" decode args r (by decide)
#print axioms mark2

theorem mark3 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark3" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark3" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark3" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark3" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark3" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark3" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark3" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark3" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark3" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark3" decode args r (by decide)
#print axioms mark3

theorem mark4 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark4" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark4" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark4" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark4" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark4" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark4" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark4" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark4" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark4" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark4" decode args r (by decide)
#print axioms mark4

theorem mark5 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark5" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark5" terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark5" mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark5" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark5" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark5" arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark5" circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark5" circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark5" decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark5" decode args r (by decide)
#print axioms mark5
end AspisR1.NNG_CheckedCalls136
