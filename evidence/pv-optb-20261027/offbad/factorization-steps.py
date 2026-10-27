import pathlib, subprocess
p=pathlib.Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OptB_OffBad.lean')
steps=[('decoder_implies_off_bad', '''theorem decoder_implies_off_bad {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop)
    (decoder : Public → World → Coins → Option Event)
    (law : ∀ w os coins, ¬ bad w os coins → signal w os coins = decoder (pub w) os coins) :
    IndependentOffBad pub signal bad := by
  intro w u same os coins hw hu
  rw [law w os coins hw, law u os coins hu, same]
'''),('decoder_of_off_bad', '''theorem decoder_of_off_bad {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop) (h : IndependentOffBad pub signal bad) :
    ∃ decoder : Public → World → Coins → Option Event,
      ∀ w os coins, ¬ bad w os coins → signal w os coins = decoder (pub w) os coins := by
  classical
  let decoder := fun p os coins =>
    if exists_good : ∃ w, pub w = p ∧ ¬ bad w os coins then
      signal (Classical.choose exists_good) os coins else none
  refine ⟨decoder, ?_⟩
  intro w os coins good
  dsimp only [decoder]
  rw [dif_pos ⟨w,rfl,good⟩]
  exact h w _ (Classical.choose_spec (show ∃ u, pub u = pub w ∧ ¬ bad u os coins from ⟨w,rfl,good⟩)).1.symm
    os coins good (Classical.choose_spec (show ∃ u, pub u = pub w ∧ ¬ bad u os coins from ⟨w,rfl,good⟩)).2
'''),('off_bad_iff_decoder', '''theorem off_bad_iff_decoder {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop) :
    IndependentOffBad pub signal bad ↔
    ∃ decoder : Public → World → Coins → Option Event,
      ∀ w os coins, ¬ bad w os coins → signal w os coins = decoder (pub w) os coins := by
  constructor
  · exact decoder_of_off_bad pub signal bad
  · rintro ⟨decoder,law⟩
    exact decoder_implies_off_bad pub signal bad decoder law
'''),('off_false_iff', '''theorem off_false_iff {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event) :
    IndependentOffBad pub signal (fun _ _ _ => False) ↔ Independent pub signal := by
  constructor
  · intro h w u same os coins
    exact h w u same os coins (fun h => h) (fun h => h)
  · intro h
    exact independent_implies_off_bad pub signal _ h
'''),('off_bad_postprocess', '''theorem off_bad_postprocess {W Public World Coins Event Event' : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop) (h : IndependentOffBad pub signal bad)
    (f : Option Event → Option Event') :
    IndependentOffBad pub (fun w os coins => f (signal w os coins)) bad := by
  intro w u same os coins hw hu
  exact congrArg f (h w u same os coins hw hu)
'''),('off_bad_restrict', '''theorem off_bad_restrict {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad larger : W → World → Coins → Prop)
    (included : ∀ w os coins, bad w os coins → larger w os coins)
    (h : IndependentOffBad pub signal bad) : IndependentOffBad pub signal larger := by
  intro w u same os coins hw hu
  exact h w u same os coins (fun hb => hw (included w os coins hb))
    (fun hb => hu (included u os coins hb))
'''),('off_bad_difference_refutes', '''theorem off_bad_difference_refutes {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (hw : ¬ bad w os coins) (hu : ¬ bad u os coins)
    (different : signal w os coins ≠ signal u os coins) :
    ¬ IndependentOffBad pub signal bad := by
  intro h
  exact different (h w u same os coins hw hu)
'''),('off_bad_failure_presence', '''theorem off_bad_failure_presence {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop) (h : IndependentOffBad pub signal bad)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (hw : ¬ bad w os coins) (hu : ¬ bad u os coins) :
    signal w os coins = none ↔ signal u os coins = none := by
  rw [h w u same os coins hw hu]
'''),('off_bad_exact_error', '''theorem off_bad_exact_error {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (bad : W → World → Coins → Prop) (h : IndependentOffBad pub signal bad)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (hw : ¬ bad w os coins) (hu : ¬ bad u os coins) (e : Event) :
    signal w os coins = some e ↔ signal u os coins = some e := by
  rw [h w u same os coins hw hu]
''')]
for a,(name,body) in enumerate(steps,44604):
 text=p.read_text();p.write_text(text.replace('end R1Z.PV_OptB_Factorization',body+'\n#print axioms '+name+'\nend R1Z.PV_OptB_Factorization'))
 r=subprocess.run(['python3','evidence/pv-optb-20261027/offbad/check.py',str(a),'R1Z/PV_OptB_OffBad'],capture_output=True,text=True)
 print(a,name,r.returncode,r.stdout[-1800:],flush=True)
 if r.returncode:break
