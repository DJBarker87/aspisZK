import R1Z.PV_L2_F6HalfInputs
import R1Z.PV_L2_F6HalfPQ
import R1Z.PV_L2_F6HalfR0
import R1Z.PV_L2_F6HalfR1
import R1Z.PV_L2_F6HalfR2
import R1Z.PV_L2_F6HalfR3
set_option autoImplicit false
namespace R1Z.PV_L2_F6Half
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def source (a h : Slice U32) : Result Bool := do
  let d ← PV_L2_F6HalfInputs.source a h
  let x01 := d.1.1
  let x1 := d.1.2.1
  let x2 := d.1.2.2.1
  let x3 := d.1.2.2.2
  let y0 := d.2.1
  let y1 := d.2.2.1
  let y2 := d.2.2.2.1
  let y3 := d.2.2.2.2
  let pq ← PV_L2_F6HalfPQ.source x2 x3 y2 y3
  let r0 ← PV_L2_F6HalfR0.source x01 x1 y0 y1 pq.1 pq.2
  let r1 ← PV_L2_F6HalfR1.source x01 x1 y0 y1 pq.1 pq.2
  let r2 ← PV_L2_F6HalfR2.source x01 x1 x2 x3 y0 y1 y2 y3
  let r3 ← PV_L2_F6HalfR3.source x01 x1 x2 x3 y0 y1 y2 y3
  ok ((((r0 = 1#u64) && (r1 = 0#u64)) && (r2 = 0#u64)) && (r3 = 0#u64))

def recorded (a h : Slice U32) : Recorded Bool := do
  let d ← PV_L2_F6HalfInputs.recorded a h
  let x01 := d.1.1
  let x1 := d.1.2.1
  let x2 := d.1.2.2.1
  let x3 := d.1.2.2.2
  let y0 := d.2.1
  let y1 := d.2.2.1
  let y2 := d.2.2.2.1
  let y3 := d.2.2.2.2
  let pq ← PV_L2_F6HalfPQ.recorded x2 x3 y2 y3
  let r0 ← PV_L2_F6HalfR0.recorded x01 x1 y0 y1 pq.1 pq.2
  let r1 ← PV_L2_F6HalfR1.recorded x01 x1 y0 y1 pq.1 pq.2
  let r2 ← PV_L2_F6HalfR2.recorded x01 x1 x2 x3 y0 y1 y2 y3
  let r3 ← PV_L2_F6HalfR3.recorded x01 x1 x2 x3 y0 y1 y2 y3
  operation (.guard 39 0 0 ((((r0 = 1#u64) && (r1 = 0#u64)) && (r2 = 0#u64)) && (r3 = 0#u64))) (ok ((((r0 = 1#u64) && (r1 = 0#u64)) && (r2 = 0#u64)) && (r3 = 0#u64)))

theorem recorded_erases (a h : Slice U32) : (recorded a h).value = source a h := by
  simp only [recorded,source,PV_L2_RecordCompact.bind_value,
    PV_L2_F6HalfInputs.erases,    PV_L2_F6HalfPQ.erases,    PV_L2_F6HalfR0.erases,    PV_L2_F6HalfR1.erases,    PV_L2_F6HalfR2.erases,    PV_L2_F6HalfR3.erases,operation_value,bind_tc_ok]
#print axioms recorded_erases

theorem source_eq (a h : Slice U32) : source a h = half_ok a h := by
  simp only [source,half_ok,PV_L2_F6HalfInputs.source,PV_L2_F6HalfShift.source,
    PV_L2_F6HalfPQ.source,PV_L2_F6HalfR0.source,PV_L2_F6HalfR1.source,
    PV_L2_F6HalfR2.source,PV_L2_F6HalfR3.source,bind_assoc_eq,bind_tc_ok]

theorem erases (a h : Slice U32) : (recorded a h).value = half_ok a h :=
  (recorded_erases a h).trans (source_eq a h)
#print axioms source_eq
#print axioms erases
end R1Z.PV_L2_F6Half
