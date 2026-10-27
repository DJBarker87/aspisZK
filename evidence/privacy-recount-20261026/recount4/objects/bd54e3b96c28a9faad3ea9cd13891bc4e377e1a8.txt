import R1Z.PhaseMessageDependenciesBin
import R1Z.WireLengthsR1PBin
import R1RecordFrameCodec
import R1FoldedLeafCodec

/-! Logical protocol messages selected from the existing honest view. The
field codec is explicit; `wideBytes` specializes it to the existing exact-wide
codec. Auxiliary metadata is never passed to a field encoder. This constructs
a protocol model; identity with an arbitrary R1Wire base is not asserted. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseMessageEncodingBin
open R0P R0P.SemSource R0Z R0Z.HonestView R0Z.MaskLayout R0Z.FsStatement
  R1Z.Batched R1Z.GamesR1 R1Z.PhaseLocalityBin R1Z.PhaseScheduleBin
  R1Z.TranscriptR1 R1Z.PhaseBuilderDependenciesBin R1Z.PhaseMessageDependenciesBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

def wideBytes (x : AspisWideTower.WideExact) : List UInt8 :=
  (AspisR1.FoldedLeafCodec.encodeWide x).map UInt8.ofFin

def encoded (enc : K → List UInt8) {n : ℕ} (values : Fin n → K) : List UInt8 :=
  AspisR1.FixedWidthDecoder.encode enc values

/-- Existing tagged length framing, transported between the two byte carriers. -/
def framed (tag : UInt8) (payload : List UInt8) : List UInt8 :=
  (AspisR1.RecordFrameCodec.frame tag.toFin (payload.map UInt8.toFin)).map UInt8.ofFin

def semantic (enc : K → List UInt8) (p : Payload K R1Bat)
    (root : OracleAnswer) (i : Fin 27) : List UInt8 :=
  if i.val = 2 then R1Z.LensR1.ans root
  else if i.val = 14 then enc (p .maskSum)
  else if hi : 15 ≤ i.val ∧ i.val ≤ 24 then
    encoded enc (fun c : Fin 28 => p (.semanticCoeff ⟨i.val-15, by omega⟩ c))
  else if i.val = 25 then
    (List.ofFn (fun j : Fin 3 => encoded enc (fun c : Fin 29 => p (.pointClaim j c)))).flatten ++
      encoded enc (fun c : Fin 29 => p (.extraClaim c))
  else if i.val = 26 then encoded enc (fun c : Fin 29 => p (.ood 0 c))
  else []

def frame (enc : K → List UInt8) (v : ZkStatement.View K CommitHandle Aux R1Bat)
    (root : OracleAnswer) (i : Fin 27) : List UInt8 :=
  framed (WireLengthsR1PBin.semanticTag i) (semantic enc v.2 root i)

def opening (enc : K → List UInt8) (p : Payload K R1Bat)
    (root : OracleAnswer) (i : Fin 4) : List UInt8 :=
  if i.val = 0 then encoded enc (fun c : Fin 29 => p (.ood 1 c))
  else if i.val = 1 then enc (p .inactiveSum)
  else if i.val = 2 then encoded enc (fun c : Fin 7 => p (.bat (.round0 c)))
  else R1Z.LensR1.ans root ++ encoded enc (fun c : Fin 7 => p (.bat (.round1 c)))

def payload (enc : K → List UInt8) (v : ZkStatement.View K CommitHandle Aux R1Bat)
    (root : OracleAnswer) (i : Fin 4) : List UInt8 := opening enc v.2 root i

def final (enc : K → List UInt8) (v : ZkStatement.View K CommitHandle Aux R1Bat) : List UInt8 :=
  encoded enc (fun c : Fin 64 => v.2 (.bat (.final c)))

/-- The entire encoded transcript is independent of arbitrary auxiliary output. -/
theorem auxiliary_irrelevant (enc : K → List UInt8)
    (m m' : ZkStatement.Meta K CommitHandle Aux) (p : Payload K R1Bat)
    (root : OracleAnswer) :
    frame enc (m,p) root = frame enc (m',p) root ∧
    payload enc (m,p) root = payload enc (m',p) root ∧
    final enc (m,p) = final enc (m',p) := ⟨rfl, rfl, rfl⟩

theorem prepared_prefix (pub : Public K) (B : PackBasis F) (t : Trace K)
    (r : AffTape K F) (ch ch' : Challenges K) (n : ℕ) (hn : 2 ≤ n)
    (he : SemPrefix n ch ch') :
    applyAff B (prepare pub t ch) r = applyAff B (prepare pub t ch') r := by
  rw [prepare_local pub t ch ch' (he 0 (by omega)) (he 1 (by omega))]

theorem alpha_prefix (ch ch' : Challenges K) (he : SemPrefix 25 ch ch') :
    R0Z.HonestView.alpha ch = R0Z.HonestView.alpha ch' := by
  funext i
  exact he ⟨15+i.val, by omega⟩ (by dsimp; omega)

attribute [local irreducible] encoded framed

theorem semantic_prefix (enc : K → List UInt8) (π : Fin 1024 ≃ Fin 1024)
    (pub : Public K) (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch ch' : Challenges K) (root root' : OracleAnswer) (i : Fin 27)
    (he : SemPrefix i.val ch ch') (hr : i.val = 2 → root = root')
    (hc : i.val = 26 → ch.circle 0 = ch'.circle 0) :
    semantic enc (run π pub B t ch r) root i =
      semantic enc (run π pub B t ch' r) root' i := by
  unfold semantic
  split
  · rw [hr (by assumption)]
  · split
    · have hp := prepared_prefix pub B t r ch ch' i.val (by omega) he
      simp only [run, hp]
    · split
      · apply congrArg (encoded enc)
        funext c
        apply semanticCoeff_prefix
        intro j hj
        apply he
        dsimp at hj ⊢
        omega
      · split
        · have hp := prepared_prefix pub B t r ch ch' i.val (by omega) he
          have ha := alpha_prefix ch ch' (by simpa only [‹i.val = 25›] using he)
          simp only [run, hp, ha]
        · split
          · have hp := prepared_prefix pub B t r ch ch' i.val (by omega) he
            simp only [run, hp, hc (by assumption)]
          · rfl

theorem opening_prefix (enc : K → List UInt8) (π : Fin 1024 ≃ Fin 1024)
    (pub : Public K) (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch ch' : Challenges K) (root root' : OracleAnswer) (i : Fin 4)
    (hs : ch.sem = ch'.sem) (hc : ch.circle = ch'.circle)
    (ho : ∀ j : Fin 4, j.val < i.val → ch.opening j = ch'.opening j)
    (hr : i.val = 3 → root = root') :
    opening enc (run π pub B t ch r) root i =
      opening enc (run π pub B t ch' r) root' i := by
  have hp := prepared_prefix pub B t r ch ch' 25 (by omega) (fun _ _ => congrFun hs _)
  unfold opening
  split
  · simp only [run, hp, hc]
  · split
    · simp only [run, hp, ho 0 (by omega)]
    · split
      · apply congrArg (encoded enc)
        funext c
        simp only [run, hp]
        apply round0_prefix π ch ch' _ c hs hc (ho 0 (by omega)) (ho 1 (by omega))
      · rw [hr (by omega)]
        apply congrArg (fun bs => R1Z.LensR1.ans root' ++ bs)
        apply congrArg (encoded enc)
        funext c
        simp only [run, hp]
        apply round1_prefix π ch ch' _ c hs hc
          (ho 0 (by omega)) (ho 1 (by omega)) (ho 2 (by omega))

theorem final_prefix (enc : K → List UInt8) (π : Fin 1024 ≃ Fin 1024)
    (pub : Public K) (B : PackBasis F) (t : Trace K) (r : AffTape K F)
    (ch ch' : Challenges K) (hs : SemPrefix 2 ch ch')
    (ho : ∀ j : Fin 4, ch.opening j = ch'.opening j) :
    encoded enc (fun c : Fin 64 => run (Bat := R1Bat) π pub B t ch r (.bat (.final c))) =
      encoded enc (fun c : Fin 64 => run (Bat := R1Bat) π pub B t ch' r (.bat (.final c))) := by
  have hp := prepared_prefix pub B t r ch ch' 2 (by omega) hs
  apply congrArg (encoded enc)
  funext c
  simp only [run, hp]
  exact PhaseMessageDependenciesBin.final_prefix π ch ch' _ c (ho 0) (ho 2) (ho 3)

/-- Locality of semantic challenge values, directly from preceding squeezes. -/
theorem semantic_before (W : R1Wire K CommitHandle Aux) (hd : DecodeLocal W.dec)
    (tr tr' : TRead → OracleAnswer) (i : Fin 27)
    (he : SqAgree (transcriptStage (.absS i)) tr tr') :
    SemPrefix i.val (chOf W tr) (chOf W tr') := by
  intro j hj
  apply hd.sem
  apply he (.sqS ⟨j.val, by omega⟩) trivial
  simp only [transcriptStage]
  split <;> split <;> omega

theorem frame_local (enc : K → List UInt8) (W : R1Wire K CommitHandle Aux)
    (hd : DecodeLocal W.dec) (h : JointView.HonestProver K) (B : PackBasis F)
    (outputs : JointView.Statement K CommitHandle → Challenges K → Aux)
    (x : JointView.Statement K CommitHandle) (w : h.Instance) (τ : JointView.Tape K F)
    (tr tr' : TRead → OracleAnswer) (root root' : OracleAnswer) (i : Fin 27)
    (he : SqAgree (transcriptStage (.absS i)) tr tr') (hr : i.val = 2 → root = root') :
    frame enc (JointView.view h B outputs x w (chOf W tr) τ) root i =
      frame enc (JointView.view h B outputs x w (chOf W tr') τ) root' i := by
  unfold frame
  apply congrArg (framed (WireLengthsR1PBin.semanticTag i))
  apply semantic_prefix enc h.transport x.1 B (applyEligible (h.build w) τ.2) τ.1
    (chOf W tr) (chOf W tr') root root' i (semantic_before W hd tr tr' i he) hr
  intro hi
  apply hd.circle
  apply he (.sqS 25) trivial
  simp only [transcriptStage, hi]
  decide

/-- Install the actual message selectors in a wire's other data. -/
def wireData (enc : K → List UInt8) (base : R1Wire K CommitHandle Aux) :
    R1Wire K CommitHandle Aux :=
  { base with frame := frame enc, payload := payload enc, final := final enc }

theorem payload_local (enc : K → List UInt8) (W : R1Wire K CommitHandle Aux)
    (hd : DecodeLocal W.dec) (h : JointView.HonestProver K) (B : PackBasis F)
    (outputs : JointView.Statement K CommitHandle → Challenges K → Aux)
    (x : JointView.Statement K CommitHandle) (w : h.Instance) (τ : JointView.Tape K F)
    (tr tr' : TRead → OracleAnswer) (root root' : OracleAnswer) (i : Fin 4)
    (he : SqAgree (transcriptStage (.absO i)) tr tr') (hr : i.val = 3 → root = root') :
    payload enc (JointView.view h B outputs x w (chOf W tr) τ) root i =
      payload enc (JointView.view h B outputs x w (chOf W tr') τ) root' i := by
  apply opening_prefix enc h.transport x.1 B (applyEligible (h.build w) τ.2) τ.1
    (chOf W tr) (chOf W tr') root root' i
  · funext j
    apply hd.sem
    apply he (.sqS ⟨j.val, by omega⟩) trivial
    simp only [transcriptStage]
    split <;> split <;> omega
  · funext j
    apply hd.circle
    apply he (.sqS ⟨25+j.val, by omega⟩) trivial
    simp only [transcriptStage]
    split <;> split <;> omega
  · intro j hj
    apply hd.opening
    apply he (.sqO j) trivial
    simp only [transcriptStage]
    split <;> split <;> omega
  · exact hr

theorem final_local (enc : K → List UInt8) (W : R1Wire K CommitHandle Aux)
    (hd : DecodeLocal W.dec) (h : JointView.HonestProver K) (B : PackBasis F)
    (outputs : JointView.Statement K CommitHandle → Challenges K → Aux)
    (x : JointView.Statement K CommitHandle) (w : h.Instance) (τ : JointView.Tape K F)
    (tr tr' : TRead → OracleAnswer) (he : SqAgree (transcriptStage .absQ) tr tr') :
    final enc (JointView.view h B outputs x w (chOf W tr) τ) =
      final enc (JointView.view h B outputs x w (chOf W tr') τ) := by
  apply final_prefix enc h.transport x.1 B (applyEligible (h.build w) τ.2) τ.1
    (chOf W tr) (chOf W tr')
  · intro j hj
    apply hd.sem
    apply he (.sqS ⟨j.val, by omega⟩) trivial
    simp only [transcriptStage]
    split <;> omega
  · intro j
    apply hd.opening
    apply he (.sqO j) trivial
    simp only [transcriptStage]
    split <;> omega

/-- A phase inhabitant for this explicit logical encoder, retaining the supplied
block-local decoder. This is not a coercion from an arbitrary endpoint wire. -/
def phaseWire (enc : K → List UInt8) (base : R1Wire K CommitHandle Aux)
    (hd : DecodeLocal base.dec) (h : JointView.HonestProver K) (B : PackBasis F)
    (outputs : JointView.Statement K CommitHandle → Challenges K → Aux)
    (x : JointView.Statement K CommitHandle) : R1PhaseWire h B outputs x where
  toWire := wireData enc base
  decode_local := hd
  frame_local := frame_local enc base hd h B outputs x
  payload_local := payload_local enc base hd h B outputs x
  final_local := final_local enc base hd h B outputs x

#print axioms payload_local
#print axioms final_local
#print axioms phaseWire
#print axioms auxiliary_irrelevant
#print axioms prepared_prefix
#print axioms alpha_prefix
#print axioms semantic_prefix
#print axioms opening_prefix
#print axioms final_prefix
#print axioms semantic_before
#print axioms frame_local
end R1Z.PhaseMessageEncodingBin
