import NNG_Row136Fold
set_option autoImplicit false
namespace AspisR1.NNG_Row136Occurrences
open RSL NNG_Row136Fold

/-- Equality of the COMPLETE occurrence relation with the VLib field, proved
by their common deterministic CLOSED-model graph. The domain is preserved
verbatim on both sides; no child success is assumed. -/
theorem child_at {A B : Type} (field : Child A B) (arg : A)
    (call : Spec B) (model : Env → Obs B)
    (source : ∀ env o, call env o ↔ field.dom arg ∧ o = model env)
    (graph : field.dom arg → ∀ env o, field.law arg env o ↔ o = model env) :
    call = field.run arg := by
  funext env o
  apply propext
  constructor
  · intro h
    obtain ⟨hd,ho⟩ := (source env o).mp h
    exact ⟨hd, (graph hd env o).mpr ho⟩
  · intro h
    exact (source env o).mpr ⟨h.1, (graph h.1 env o).mp h.2⟩
#print axioms child_at

/-- rounds: source call equals its corresponding VLib field whenever both
are the graph of the SAME CLOSED deterministic model. -/
theorem rounds (VL : VLib) (c : Calls VL) (p : VL.Prefix) (t : VL.Transcript)
    (model : Env → Obs (Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)))
    (source : ∀ env o, c.semanticRounds (p,t) env o ↔ VL.semanticRounds.dom (p,t) ∧ o = model env)
    (graph : VL.semanticRounds.dom (p,t) → ∀ env o,
      VL.semanticRounds.law (p,t) env o ↔ o = model env) :
    c.semanticRounds (p,t) = VL.semanticRounds.run (p,t) :=
  child_at VL.semanticRounds (p,t) (c.semanticRounds (p,t)) model source graph
#print axioms rounds

/-- claims: source call equals its corresponding VLib field whenever both
are the graph of the SAME CLOSED deterministic model. -/
theorem claims (VL : VLib) (c : Calls VL) (p : VL.Prefix)
    (model : Env → Obs (Except VL.WErr VL.Claims))
    (source : ∀ env o, c.claims p env o ↔ VL.claims.dom p ∧ o = model env)
    (graph : VL.claims.dom p → ∀ env o,
      VL.claims.law p env o ↔ o = model env) :
    c.claims p = VL.claims.run p :=
  child_at VL.claims p (c.claims p) model source graph
#print axioms claims

/-- terminal: source call equals its corresponding VLib field whenever both
are the graph of the SAME CLOSED deterministic model. -/
theorem terminal (VL : VLib) (c : Calls VL) (pub : VL.Public) (claims : VL.Claims) (alpha : VL.Alpha) (orig : VL.OrigChallenges)
    (model : Env → Obs (Except Unit VL.QM31))
    (source : ∀ env o, c.terminalQm31 (pub,claims,alpha,orig) env o ↔ VL.terminalQm31.dom (pub,claims,alpha,orig) ∧ o = model env)
    (graph : VL.terminalQm31.dom (pub,claims,alpha,orig) → ∀ env o,
      VL.terminalQm31.law (pub,claims,alpha,orig) env o ↔ o = model env) :
    c.terminalQm31 (pub,claims,alpha,orig) = VL.terminalQm31.run (pub,claims,alpha,orig) :=
  child_at VL.terminalQm31 (pub,claims,alpha,orig) (c.terminalQm31 (pub,claims,alpha,orig)) model source graph
#print axioms terminal

/-- circle0: source call equals its corresponding VLib field whenever both
are the graph of the SAME CLOSED deterministic model. -/
theorem circle0 (VL : VLib) (c : Calls VL) (t1 : VL.Transcript) (rec25 : VL.Record)
    (model : Env → Obs (Except VL.WErr (VL.Point × VL.Transcript)))
    (source : ∀ env o, c.circle (t1,rec25) env o ↔ VL.circle.dom (t1,rec25) ∧ o = model env)
    (graph : VL.circle.dom (t1,rec25) → ∀ env o,
      VL.circle.law (t1,rec25) env o ↔ o = model env) :
    c.circle (t1,rec25) = VL.circle.run (t1,rec25) :=
  child_at VL.circle (t1,rec25) (c.circle (t1,rec25)) model source graph
#print axioms circle0

/-- circle1: source call equals its corresponding VLib field whenever both
are the graph of the SAME CLOSED deterministic model. -/
theorem circle1 (VL : VLib) (c : Calls VL) (t2 : VL.Transcript) (rec26 : VL.Record)
    (model : Env → Obs (Except VL.WErr (VL.Point × VL.Transcript)))
    (source : ∀ env o, c.circle (t2,rec26) env o ↔ VL.circle.dom (t2,rec26) ∧ o = model env)
    (graph : VL.circle.dom (t2,rec26) → ∀ env o,
      VL.circle.law (t2,rec26) env o ↔ o = model env) :
    c.circle (t2,rec26) = VL.circle.run (t2,rec26) :=
  child_at VL.circle (t2,rec26) (c.circle (t2,rec26)) model source graph
#print axioms circle1

/-- mask: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem mask (VL : VLib) (c : Calls VL) (claims : VL.Claims) (alpha : VL.Alpha) (model : VL.QM31)
    (source : c.maskValue claims alpha = model)
    (graph : VL.maskValue claims alpha = model) :
    c.maskValue claims alpha = VL.maskValue claims alpha := source.trans graph.symm
#print axioms mask

/-- record25: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem record25 (VL : VLib) (c : Calls VL) (p : VL.Prefix) (model : Except VL.WErr VL.Record)
    (source : c.validatedRecord p 25 = model)
    (graph : VL.validatedRecord p 25 = model) :
    c.validatedRecord p 25 = VL.validatedRecord p 25 := source.trans graph.symm
#print axioms record25

/-- extra: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem extra (VL : VLib) (c : Calls VL) (rec25 : VL.Record) (model : Except VL.WErr VL.K29)
    (source : c.decodeK29 rec25 87 = model)
    (graph : VL.decodeK29 rec25 87 = model) :
    c.decodeK29 rec25 87 = VL.decodeK29 rec25 87 := source.trans graph.symm
#print axioms extra

/-- multiply: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem multiply (VL : VLib) (c : Calls VL) (eta terminal : VL.QM31) (model : VL.QM31)
    (source : c.qmul eta terminal = model)
    (graph : VL.qmul eta terminal = model) :
    c.qmul eta terminal = VL.qmul eta terminal := source.trans graph.symm
#print axioms multiply

/-- addMask: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem addMask (VL : VLib) (c : Calls VL) (mask product : VL.QM31) (model : VL.QM31)
    (source : c.qadd mask product = model)
    (graph : VL.qadd mask product = model) :
    c.qadd mask product = VL.qadd mask product := source.trans graph.symm
#print axioms addMask

/-- addExtra: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem addExtra (VL : VLib) (c : Calls VL) (maskedPart at28 : VL.QM31) (model : VL.QM31)
    (source : c.qadd maskedPart at28 = model)
    (graph : VL.qadd maskedPart at28 = model) :
    c.qadd maskedPart at28 = VL.qadd maskedPart at28 := source.trans graph.symm
#print axioms addExtra

/-- record25_reused: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem record25_reused (VL : VLib) (c : Calls VL) (p : VL.Prefix) (model : Except VL.WErr VL.Record)
    (source : c.validatedRecord p 25 = model)
    (graph : VL.validatedRecord p 25 = model) :
    c.validatedRecord p 25 = VL.validatedRecord p 25 := source.trans graph.symm
#print axioms record25_reused

/-- record26: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem record26 (VL : VLib) (c : Calls VL) (p : VL.Prefix) (model : Except VL.WErr VL.Record)
    (source : c.validatedRecord p 26 = model)
    (graph : VL.validatedRecord p 26 = model) :
    c.validatedRecord p 26 = VL.validatedRecord p 26 := source.trans graph.symm
#print axioms record26

/-- beforeZ1: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem beforeZ1 (VL : VLib) (c : Calls VL) (rec26 : VL.Record) (model : Except VL.WErr VL.K29)
    (source : c.decodeK29 rec26 0 = model)
    (graph : VL.decodeK29 rec26 0 = model) :
    c.decodeK29 rec26 0 = VL.decodeK29 rec26 0 := source.trans graph.symm
#print axioms beforeZ1

/-- record26_reused: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem record26_reused (VL : VLib) (c : Calls VL) (p : VL.Prefix) (model : Except VL.WErr VL.Record)
    (source : c.validatedRecord p 26 = model)
    (graph : VL.validatedRecord p 26 = model) :
    c.validatedRecord p 26 = VL.validatedRecord p 26 := source.trans graph.symm
#print axioms record26_reused

/-- payload2: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem payload2 (VL : VLib) (c : Calls VL) (p : VL.Prefix) (model : Except VL.WErr Bytes)
    (source : c.payload p 2 = model)
    (graph : VL.payload p 2 = model) :
    c.payload p 2 = VL.payload p 2 := source.trans graph.symm
#print axioms payload2

end AspisR1.NNG_Row136Occurrences
