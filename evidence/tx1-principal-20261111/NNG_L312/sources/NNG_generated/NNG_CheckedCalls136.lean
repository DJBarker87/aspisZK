import NNG_TypedDomains136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckedCalls136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_TypedDomains136

theorem terminal {Reply : Type} (args : Public × Claims × Alpha × aspis_core.state_only_prefix.r0.Challenges) (r : Result Reply) (domain : NNG_TypedDomains136.terminal args) :
    Checked (.call "terminal" args r) := by
  constructor
  · exact (same "terminal" NNG_TypedDomains136.terminal args r).mpr domain
  · exact NNG_TypedDomains136.other "mask" "terminal" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "terminal" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "terminal" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "terminal" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "terminal" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "terminal" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "terminal" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "terminal" NNG_TypedDomains136.decode args r (by decide)
#print axioms terminal

theorem mask {Reply : Type} (args : Array Q 16#usize × Alpha × Q × Alpha) (r : Result Reply) (domain : NNG_TypedDomains136.mask args) :
    Checked (.call "mask" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mask" NNG_TypedDomains136.terminal args r (by decide)
  · exact (same "mask" NNG_TypedDomains136.mask args r).mpr domain
  · exact NNG_TypedDomains136.other "multiply" "mask" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mask" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mask" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mask" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mask" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mask" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mask" NNG_TypedDomains136.decode args r (by decide)
#print axioms mask

theorem multiply {Reply : Type} (args : Q × Q) (r : Result Reply) (domain : NNG_TypedDomains136.arithmetic args) :
    Checked (.call "multiply" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "multiply" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "multiply" NNG_TypedDomains136.mask args r (by decide)
  · exact (same "multiply" NNG_TypedDomains136.arithmetic args r).mpr domain
  · exact NNG_TypedDomains136.other "addMask" "multiply" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "multiply" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "multiply" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "multiply" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "multiply" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "multiply" NNG_TypedDomains136.decode args r (by decide)
#print axioms multiply

theorem addMask {Reply : Type} (args : Q × Q) (r : Result Reply) (domain : NNG_TypedDomains136.arithmetic args) :
    Checked (.call "addMask" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "addMask" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "addMask" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "addMask" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact (same "addMask" NNG_TypedDomains136.arithmetic args r).mpr domain
  · exact NNG_TypedDomains136.other "addExtra" "addMask" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "addMask" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "addMask" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "addMask" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "addMask" NNG_TypedDomains136.decode args r (by decide)
#print axioms addMask

theorem addExtra {Reply : Type} (args : Q × Q) (r : Result Reply) (domain : NNG_TypedDomains136.arithmetic args) :
    Checked (.call "addExtra" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "addExtra" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "addExtra" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "addExtra" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "addExtra" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact (same "addExtra" NNG_TypedDomains136.arithmetic args r).mpr domain
  · exact NNG_TypedDomains136.other "circle0" "addExtra" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "addExtra" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "addExtra" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "addExtra" NNG_TypedDomains136.decode args r (by decide)
#print axioms addExtra

theorem circle0 {Reply : Type} (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) (r : Result Reply) (domain : NNG_TypedDomains136.circle args) :
    Checked (.call "circle0" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "circle0" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "circle0" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "circle0" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "circle0" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "circle0" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact (same "circle0" NNG_TypedDomains136.circle args r).mpr domain
  · exact NNG_TypedDomains136.other "circle1" "circle0" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "circle0" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "circle0" NNG_TypedDomains136.decode args r (by decide)
#print axioms circle0

theorem circle1 {Reply : Type} (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) (r : Result Reply) (domain : NNG_TypedDomains136.circle args) :
    Checked (.call "circle1" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "circle1" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "circle1" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "circle1" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "circle1" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "circle1" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "circle1" NNG_TypedDomains136.circle args r (by decide)
  · exact (same "circle1" NNG_TypedDomains136.circle args r).mpr domain
  · exact NNG_TypedDomains136.other "extra" "circle1" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "circle1" NNG_TypedDomains136.decode args r (by decide)
#print axioms circle1

theorem extra {Reply : Type} (args : r1_wire.ValidatedRecord × Usize) (r : Result Reply) (domain : NNG_TypedDomains136.decode args) :
    Checked (.call "extra" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "extra" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "extra" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "extra" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "extra" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "extra" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "extra" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "extra" NNG_TypedDomains136.circle args r (by decide)
  · exact (same "extra" NNG_TypedDomains136.decode args r).mpr domain
  · exact NNG_TypedDomains136.other "beforeZ1" "extra" NNG_TypedDomains136.decode args r (by decide)
#print axioms extra

theorem beforeZ1 {Reply : Type} (args : r1_wire.ValidatedRecord × Usize) (r : Result Reply) (domain : NNG_TypedDomains136.decode args) :
    Checked (.call "beforeZ1" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "beforeZ1" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "beforeZ1" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "beforeZ1" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "beforeZ1" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "beforeZ1" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "beforeZ1" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "beforeZ1" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "beforeZ1" NNG_TypedDomains136.decode args r (by decide)
  · exact (same "beforeZ1" NNG_TypedDomains136.decode args r).mpr domain
#print axioms beforeZ1

theorem rounds {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "rounds" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "rounds" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "rounds" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "rounds" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "rounds" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "rounds" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "rounds" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "rounds" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "rounds" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "rounds" NNG_TypedDomains136.decode args r (by decide)
#print axioms rounds

theorem claims {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "claims" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "claims" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "claims" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "claims" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "claims" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "claims" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "claims" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "claims" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "claims" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "claims" NNG_TypedDomains136.decode args r (by decide)
#print axioms claims

theorem record25 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "record25" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "record25" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "record25" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "record25" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "record25" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "record25" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "record25" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "record25" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "record25" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "record25" NNG_TypedDomains136.decode args r (by decide)
#print axioms record25

theorem record26 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "record26" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "record26" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "record26" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "record26" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "record26" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "record26" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "record26" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "record26" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "record26" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "record26" NNG_TypedDomains136.decode args r (by decide)
#print axioms record26

theorem state {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "state" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "state" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "state" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "state" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "state" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "state" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "state" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "state" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "state" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "state" NNG_TypedDomains136.decode args r (by decide)
#print axioms state

theorem payload2 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "payload2" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "payload2" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "payload2" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "payload2" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "payload2" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "payload2" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "payload2" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "payload2" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "payload2" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "payload2" NNG_TypedDomains136.decode args r (by decide)
#print axioms payload2

theorem mark2 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark2" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark2" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark2" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark2" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark2" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark2" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark2" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark2" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark2" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark2" NNG_TypedDomains136.decode args r (by decide)
#print axioms mark2

theorem mark3 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark3" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark3" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark3" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark3" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark3" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark3" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark3" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark3" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark3" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark3" NNG_TypedDomains136.decode args r (by decide)
#print axioms mark3

theorem mark4 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark4" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark4" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark4" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark4" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark4" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark4" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark4" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark4" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark4" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark4" NNG_TypedDomains136.decode args r (by decide)
#print axioms mark4

theorem mark5 {Args Reply : Type} (args : Args) (r : Result Reply) :
    Checked (.call "mark5" args r) := by
  constructor
  · exact NNG_TypedDomains136.other "terminal" "mark5" NNG_TypedDomains136.terminal args r (by decide)
  · exact NNG_TypedDomains136.other "mask" "mark5" NNG_TypedDomains136.mask args r (by decide)
  · exact NNG_TypedDomains136.other "multiply" "mark5" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addMask" "mark5" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "addExtra" "mark5" NNG_TypedDomains136.arithmetic args r (by decide)
  · exact NNG_TypedDomains136.other "circle0" "mark5" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "circle1" "mark5" NNG_TypedDomains136.circle args r (by decide)
  · exact NNG_TypedDomains136.other "extra" "mark5" NNG_TypedDomains136.decode args r (by decide)
  · exact NNG_TypedDomains136.other "beforeZ1" "mark5" NNG_TypedDomains136.decode args r (by decide)
#print axioms mark5
end AspisR1.NNG_CheckedCalls136
