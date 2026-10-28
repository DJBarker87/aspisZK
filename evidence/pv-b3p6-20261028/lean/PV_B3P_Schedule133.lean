import Aeneas.Std
namespace PV_B3P_Schedule133
set_option autoImplicit false

-- Kind data matters only for the three private-path variants filtered below.
structure Link where
  path : Bool
  producer : Nat
  consumer : Nat
  deriving DecidableEq, Repr
inductive Error where
  | shape
  | endpointCapacity (row : Nat)
  deriving DecidableEq, Repr

def link (p c : Nat) : Link := ⟨false,p,c⟩
def path (p c : Nat) : Link := ⟨true,p,c⟩
def legacyAux (level : Nat) : Nat := 864 + level / 4 * 16 + 1 + 2 * (level % 4)
def forestAux (level : Nat) : Nat := 912 + level / 4 * 16 + 1 + 4 * (level % 4)
def forestBlock (level : Nat) : Nat := if level ≤ 20 then 4 + level else 33 + level

def legacyLinks : List Link :=
  ([(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)] : List (Nat × Nat)).map
    (fun (f,t) => link (f*16+11) (t*16)) ++
  [link 11 28,link 12 412,link 44 428,link 60 428] ++
  (List.range 21).flatMap (fun level =>
    [path ((3+level)*16+11) (legacyAux level),
     path (legacyAux level+1) ((4+level)*16+12),
     path (legacyAux level+1) ((4+level)*16)]) ++
  [link 44 960,link 460 962,link 508 964,
   link 960 966,link 962 966,link 964 967,link 966 967,
   link 64 969,link (legacyAux 0) 969,link (32*16+11) 970,
   link (29*16+11) (33*16+12),link (32*16+11) (33*16+12),link 970 (33*16)] ++
  (List.range 20).flatMap (fun level =>
    [link ((33+level)*16+11) ((34+level)*16+12),
     link ((33+level)*16+11) ((34+level)*16)])

def checkEndpoints : List Link → List Nat → List Nat → Except Error Unit
  | [],_,_ => .ok ()
  | item::tail,ps,cs =>
    if item.producer ≥ 1024 || ps.count item.producer ≥ 2 then
      .error (.endpointCapacity item.producer)
    else if item.consumer ≥ 1024 || cs.count item.consumer ≥ 2 then
      .error (.endpointCapacity item.consumer)
    else checkEndpoints tail (item.producer::ps) (item.consumer::cs)

def checked (expected : Nat) (links : List Link) : Except Error (List Link) := do
  if links.length != expected then throw .shape
  checkEndpoints links [] []
  pure links

def legacy : Except Error (List Link) := checked 127 legacyLinks

def translate (item : Link) : Link :=
  {item with producer := if item.producer ≥ 864 then item.producer+48 else item.producer,
             consumer := if item.consumer ≥ 864 then item.consumer+48 else item.consumer}

def forestLinks (legacy : List Link) : List Link :=
  (legacy.filter (fun x => !x.path)).map translate ++
  (List.range 24).flatMap (fun level =>
    let previous := if level == 0 then 3 else forestBlock (level-1)
    [path (previous*16+11) (forestAux level),
     path (forestAux level+1) (forestBlock level*16+12),
     path (forestAux level+1) (forestBlock level*16)])

def forest : Except Error (List Link) := do
  let old ← legacy
  checked 136 (forestLinks old)

theorem kind_erasure (item : Link) :
    (item.producer,item.consumer) =
    (({item with path := false} : Link).producer,({item with path := false} : Link).consumer) := rfl

theorem legacy_length : legacyLinks.length = 127 := rfl
-- Only 127/136 records and at most 272 scalar endpoints: these reductions
-- have no field arithmetic or large numeral recurrence.
theorem legacy_capacity : checkEndpoints legacyLinks [] [] = .ok () := rfl

theorem legacy_success : legacy = .ok legacyLinks := by
  simp only [legacy,checked,legacy_length,ne_eq,not_true_eq_false,Bool.false_eq_true,
    ↓reduceIte,legacy_capacity]
  rfl

theorem forest_length : (forestLinks legacyLinks).length = 136 := rfl
theorem forest_capacity : checkEndpoints (forestLinks legacyLinks) [] [] = .ok () := rfl

theorem forest_success : forest = .ok (forestLinks legacyLinks) := by
  rw [forest,legacy_success]
  change checked 136 (forestLinks legacyLinks) = _
  simp only [checked,forest_length,ne_eq,not_true_eq_false,Bool.false_eq_true,
    ↓reduceIte,forest_capacity]
  rfl

#print axioms kind_erasure
#print axioms legacy_length
#print axioms legacy_capacity
#print axioms legacy_success
#print axioms forest_length
#print axioms forest_capacity
#print axioms forest_success
end PV_B3P_Schedule133
