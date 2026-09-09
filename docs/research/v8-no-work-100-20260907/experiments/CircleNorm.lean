import ChordNorm
namespace AspisV8.CircleNorm
variable {R : Type*} [CommRing R]
def unit (p : R × R) : Prop := p.1^2+p.2^2=1
def add (p q : R × R) : R × R :=
  (p.1*q.1-p.2*q.2,p.1*q.2+p.2*q.1)

theorem add_unit (p q : R × R) (hp : unit p) (hq : unit q) :
    unit (add p q) := by
  dsimp [unit,add] at *
  calc
    _ = (p.1^2+p.2^2)*(q.1^2+q.2^2) := by ring
    _ = 1 := by rw [hp,hq]; ring

def UnitPoint (R : Type*) [CommRing R] := {p : R × R // unit p}
def append (p q : UnitPoint R) : UnitPoint R :=
  ⟨add p.val q.val, add_unit _ _ p.property q.property⟩

-- Actual log20 source has two optional group additions after a low lookup.
def windows (low middle high : UnitPoint R) (useMiddle useHigh : Bool) : UnitPoint R :=
  let first := if useMiddle then append low middle else low
  if useHigh then append first high else first

theorem windows_unit (low middle high : UnitPoint R) (m h : Bool) :
    unit (windows low middle high m h).val :=
  (windows low middle high m h).property

theorem map_unit {F : Type*} [CommRing F] (f : F →+* R)
    (x y : F) (hu : x^2+y^2=1) : (f x)^2+(f y)^2=1 := by
  have := congrArg f hu
  simpa only [map_add,map_pow,map_one] using this

-- Four source-ordered norms, including all nonreal QM31 chord coordinates.
theorem four_slots (r a b c d e f x y : R) (hu : x^2+y^2=1) :
    (ChordNorm.norm r (a+c*x+e*y) (b+d*x+f*y),
     ChordNorm.norm r (a+c*x-e*y) (b+d*x-f*y),
     ChordNorm.norm r (a-c*x-e*y) (b-d*x-f*y),
     ChordNorm.norm r (a-c*x+e*y) (b-d*x+f*y)) =
    (let t := (ChordNorm.norm r a b+ChordNorm.norm r e f) +
        (ChordNorm.norm r c d-ChordNorm.norm r e f)*x^2
     let u := ChordNorm.polar r a b c d*x
     let v := ChordNorm.polar r a b e f*y
     let w := ChordNorm.polar r c d e f*(x*y)
     ((t+u)+(v+w),(t+u)-(v+w),(t-u)-(v-w),(t-u)+(v-w))) := by
  rw [ChordNorm.four_slots]
  have he := ChordNorm.circle_even (ChordNorm.norm r a b)
    (ChordNorm.norm r c d) (ChordNorm.norm r e f) x y hu
  simpa only [ChordNorm.even,he]

theorem point_endpoint (p : UnitPoint R) (a b c : R) :
    a+b*p.val.1^2+c*p.val.2^2 =
      (a+c)+(b-c)*p.val.1^2 :=
  ChordNorm.circle_even _ _ _ _ _ p.property

-- The off-circle control must remain outside the shortcut API.
theorem off_circle_counterexample :
    (0+(0:ℤ)*0^2+1*0^2) ≠ ((0+1)+(0-1)*0^2) := by norm_num

#print axioms add_unit
#print axioms windows_unit
#print axioms map_unit
#print axioms four_slots
#print axioms point_endpoint
#print axioms off_circle_counterexample
end AspisV8.CircleNorm
