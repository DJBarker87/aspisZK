from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NNG_Row136Fold
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

'''
# Source lexical names follow NNG_SOURCE_OCCURRENCES.json. Reused getter
# values have separate source positions even though emission calls only once.
effect=[
 ('rounds','semanticRounds','(p : VL.Prefix) (t : VL.Transcript)','(p,t)','Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)'),
 ('claims','claims','(p : VL.Prefix)','p','Except VL.WErr VL.Claims'),
 ('terminal','terminalQm31','(pub : VL.Public) (claims : VL.Claims) (alpha : VL.Alpha) (orig : VL.OrigChallenges)','(pub,claims,alpha,orig)','Except Unit VL.QM31'),
 ('circle0','circle','(t1 : VL.Transcript) (rec25 : VL.Record)','(t1,rec25)','Except VL.WErr (VL.Point × VL.Transcript)'),
 ('circle1','circle','(t2 : VL.Transcript) (rec26 : VL.Record)','(t2,rec26)','Except VL.WErr (VL.Point × VL.Transcript)')]
for name,field,args,arg,ret in effect:
 s+=f'''/-- {name}: source call equals its corresponding VLib field whenever both
are the graph of the SAME CLOSED deterministic model. -/
theorem {name} (VL : VLib) (c : Calls VL) {args}
    (model : Env → Obs ({ret}))
    (source : ∀ env o, c.{field} {arg} env o ↔ VL.{field}.dom {arg} ∧ o = model env)
    (graph : VL.{field}.dom {arg} → ∀ env o,
      VL.{field}.law {arg} env o ↔ o = model env) :
    c.{field} {arg} = VL.{field}.run {arg} :=
  child_at VL.{field} {arg} (c.{field} {arg}) model source graph
#print axioms {name}

'''
pure=[
 ('mask','maskValue','(claims : VL.Claims) (alpha : VL.Alpha)','claims alpha','VL.QM31'),
 ('record25','validatedRecord','(p : VL.Prefix)','p 25','Except VL.WErr VL.Record'),
 ('extra','decodeK29','(rec25 : VL.Record)','rec25 87','Except VL.WErr VL.K29'),
 ('multiply','qmul','(eta terminal : VL.QM31)','eta terminal','VL.QM31'),
 ('addMask','qadd','(mask product : VL.QM31)','mask product','VL.QM31'),
 ('addExtra','qadd','(maskedPart at28 : VL.QM31)','maskedPart at28','VL.QM31'),
 ('record25_reused','validatedRecord','(p : VL.Prefix)','p 25','Except VL.WErr VL.Record'),
 ('record26','validatedRecord','(p : VL.Prefix)','p 26','Except VL.WErr VL.Record'),
 ('beforeZ1','decodeK29','(rec26 : VL.Record)','rec26 0','Except VL.WErr VL.K29'),
 ('record26_reused','validatedRecord','(p : VL.Prefix)','p 26','Except VL.WErr VL.Record'),
 ('payload2','payload','(p : VL.Prefix)','p 2','Except VL.WErr Bytes')]
for name,field,args,arg,ret in pure:
 s+=f'''/-- {name}: the pure CLOSED-model graph fixes the complete value, including
Rust Err; it does not select only the Ok arm. -/
theorem {name} (VL : VLib) (c : Calls VL) {args} (model : {ret})
    (source : c.{field} {arg} = model)
    (graph : VL.{field} {arg} = model) :
    c.{field} {arg} = VL.{field} {arg} := source.trans graph.symm
#print axioms {name}

'''
s+='end AspisR1.NNG_Row136Occurrences\n'
(E/'NNG_Row136Occurrences.lean').write_text(s)
