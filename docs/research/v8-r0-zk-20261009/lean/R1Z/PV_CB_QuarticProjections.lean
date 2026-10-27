import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace R1Z.PV_CB_QuarticProjections
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31

def word0 (q : Q) : U32 := q.c0.a
def word1 (q : Q) : U32 := q.c0.b
def word2 (q : Q) : U32 := q.c1.a
def word3 (q : Q) : U32 := q.c1.b

theorem value_ext (a b : Q)
    (h0 : word0 a = word0 b) (h1 : word1 a = word1 b)
    (h2 : word2 a = word2 b) (h3 : word3 a = word3 b) : a = b := by
  cases a with | mk a0 a1 =>
    cases b with | mk b0 b1 =>
      cases a0; cases a1; cases b0; cases b1
      simp_all [word0,word1,word2,word3]

def project (word : Q → U32) (r : Result Q) : Result U32 := do
  let q ← r
  ok (word q)

/-- All four complete Result projections determine the entire Result. -/
theorem result_ext (a b : Result Q)
    (h0 : project word0 a = project word0 b)
    (h1 : project word1 a = project word1 b)
    (h2 : project word2 a = project word2 b)
    (h3 : project word3 a = project word3 b) : a = b := by
  cases a <;> cases b <;> simp_all [project]
  apply value_ext <;> assumption
#print axioms value_ext
#print axioms result_ext
end R1Z.PV_CB_QuarticProjections
