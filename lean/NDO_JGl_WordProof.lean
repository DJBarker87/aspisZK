import NDO_JGd_ExactWords
import Mathlib.Tactic
import R0P.Value
set_option autoImplicit false
namespace AspisR1.JGl_WordProof
open JGd_ExactWords
abbrev Canonical (w : W) :=
  AspisV8R17.QM31WordResidues.CanonicalPair w.1 ∧ AspisV8R17.QM31WordResidues.CanonicalPair w.2

theorem sub (x y z : W) (hy : Canonical y)
    (h : AspisV8R17.GeneratedQM31Linear.qmSubWords x y=z) : value x-value y=value z :=
  (AspisV8R17.QM31WordTower.decode_sub x y hy).symm.trans (congrArg value h)
#print axioms sub

theorem zero : (0 : Q)=value ((0,0),(0,0)) := rfl
#print axioms zero

theorem one : (1 : Q)=value ((1,0),(0,0)) := rfl
#print axioms one
end AspisR1.JGl_WordProof

open Lean Meta Elab Tactic
namespace AspisR1.JGl_WordProof
abbrev Words := (Nat × Nat) × (Nat × Nat)
def modulus : Nat := 2147483647
def plus (x y : Words) : Words :=
  (((x.1.1+y.1.1)%modulus,(x.1.2+y.1.2)%modulus),
   ((x.2.1+y.2.1)%modulus,(x.2.2+y.2.2)%modulus))
def minus (x y : Words) : Words :=
  (((x.1.1+modulus-y.1.1)%modulus,(x.1.2+modulus-y.1.2)%modulus),
   ((x.2.1+modulus-y.2.1)%modulus,(x.2.2+modulus-y.2.2)%modulus))
def times (x y : Words) : Words :=
  let cm (a b : Nat × Nat) : Nat × Nat :=
    ((a.1*b.1+modulus-(a.2*b.2)%modulus)%modulus,(a.1*b.2+a.2*b.1)%modulus)
  let ca (a b : Nat × Nat) : Nat × Nat := ((a.1+b.1)%modulus,(a.2+b.2)%modulus)
  let p := cm x.1 y.1
  let q := cm x.2 y.2
  (ca p (cm q (2,1)),ca (cm x.1 y.2) (cm x.2 y.1))

def wordExpr (w : Words) : MetaM Expr := do
  let a ← mkAppM ``Prod.mk #[mkNatLit w.1.1,mkNatLit w.1.2]
  let b ← mkAppM ``Prod.mk #[mkNatLit w.2.1,mkNatLit w.2.2]
  mkAppM ``Prod.mk #[a,b]

def proveNumeric (type : Expr) : TacticM Expr := do
  let saved ← getGoals
  let m ← mkFreshExprSyntheticOpaqueMVar type
  setGoals [m.mvarId!]
  evalTactic (← `(tactic| norm_num [Canonical,
    AspisV8R17.QM31WordResidues.CanonicalPair,
    AspisV8R17.GeneratedQM31Products.qmMulWords,
    AspisV8R17.GeneratedQM31Linear.qmAddWords,
    AspisV8R17.GeneratedQM31Linear.qmSubWords,
    AspisV8R17.GeneratedQM31Products.addWords,
    AspisV8R17.GeneratedQM31Products.subWords,
    AspisV8R17.GeneratedQM31Products.mulWords,
    AspisV8R17.GeneratedQM31Products.rWords,
    AspisV8R17.RawReducer.P]))
  unless (← getGoals).isEmpty do throwError "word certificate did not close"
  setGoals saved
  instantiateMVars m

def atomName (e : Expr) : Bool :=
  [``HAdd.hAdd,``HSub.hSub,``HMul.hMul,``Neg.neg,``HPow.hPow,
   ``OfNat.ofNat,``Nat.cast,``JGd_ExactWords.value,
   ``ExtractedMaskQM31Exact.decode,``R0P.valueReconstruct10].contains e.getAppFn.constName!

partial def reflect (cache : IO.Ref (Std.HashMap Expr (Words × Expr))) (input : Expr) : TacticM (Words × Expr) := do
  let e ← whnfHeadPred input (fun x=>pure (!atomName x))
  if let some old := (← cache.get)[e]? then return old
  let result : Words × Expr ← do
    let args := e.getAppArgs
    let head := e.getAppFn.constName!
    if [``HAdd.hAdd,``HSub.hSub,``HMul.hMul].contains head then
      let x := args[args.size-2]!
      let y := args[args.size-1]!
      let (wx,hx) ← reflect cache x
      let (wy,hy) ← reflect cache y
      let wz := if head==``HAdd.hAdd then plus wx wy else if head==``HSub.hSub then minus wx wy else times wx wy
      let ex ← wordExpr wx
      let ey ← wordExpr wy
      let ez ← wordExpr wz
      let operation := mkAppN e.getAppFn (args.extract 0 (args.size-2))
      let lifted ← mkAppM ``congrArg₂ #[operation,hx,hy]
      let law := if head==``HAdd.hAdd then ``JGd_ExactWords.add else if head==``HSub.hSub then ``sub else ``JGd_ExactWords.mul
      let mut ps := #[ex,ey,ez]
      if head==``HSub.hSub then
        let canon ← proveNumeric (← mkAppM ``Canonical #[ey])
        ps := ps.push canon
      let computation := if head==``HAdd.hAdd then ``AspisV8R17.GeneratedQM31Linear.qmAddWords
        else if head==``HSub.hSub then ``AspisV8R17.GeneratedQM31Linear.qmSubWords
        else ``AspisV8R17.GeneratedQM31Products.qmMulWords
      let call ← mkAppM computation #[ex,ey]
      let hcalc ← if let some (_,hc) := (← cache.get)[call]? then pure hc
        else do
          let hc ← proveNumeric (← mkEq call ez)
          cache.modify (fun entries=>entries.insert call (wz,hc))
          pure hc
      let result ← mkAppM law (ps.push hcalc)
      return (wz,← mkEqTrans lifted result)
    else if head==``R0P.valueReconstruct10 then
      let law ← mkAppM ``R0P.value_reconstruct10_eq #[args[args.size-1]!]
      let some (_,_,rhs) := (← inferType law).eq? | throwError "reconstruction law"
      let (w,h) ← reflect cache rhs
      return (w,← mkEqTrans law h)
    else if head==``HPow.hPow then
      let x := args[args.size-2]!
      let some n ← getNatValue? (← whnf args[args.size-1]!) | throwError "nonliteral exponent"
      let law ← if n==0 then mkAppM ``pow_zero #[x]
        else mkAppM ``pow_succ #[x,mkNatLit (n-1)]
      let some (_,_,rhs) := (← inferType law).eq? | throwError "power law"
      let (w,h) ← reflect cache rhs
      return (w,← mkEqTrans law h)
    else if head==``Neg.neg then
      let x := args[args.size-1]!
      let law ← mkAppM ``neg_eq_zero_sub #[x]
      let some (_,_,rhs) := (← inferType law).eq? | throwError "negation law"
      let (w,h) ← reflect cache rhs
      return (w,← mkEqTrans law h)
    else if head==``OfNat.ofNat || head==``Nat.cast then
      let nExpr := if head==``OfNat.ofNat then args[1]! else args[args.size-1]!
      let some n ← getNatValue? (← withTransparency .all (whnf nExpr)) | throwError "nonliteral cast {nExpr}"
      let w : Words := ((n,0),(0,0))
      let target ← mkAppM ``JGd_ExactWords.value #[← wordExpr w]
      return (w,← mkEqRefl target)
    else
      let projection (q : Expr) (path : List Nat) : MetaM Expr := do
        let mut q := q
        for i in path do q ← mkAppM (if i==0 then ``QuadraticAlgebra.re else ``QuadraticAlgebra.im) #[q]
        mkAppM ``ZMod.val #[q]
      let mut ns : Array Nat := #[]
      for path in [[0,0],[0,1],[1,0],[1,1]] do
        let term ← projection e path
        let some n ← getNatValue? (← withTransparency .all (whnf term)) | throwError "nonliteral field leaf {e} at {term}"
        ns := ns.push n
      let w : Words := ((ns[0]!,ns[1]!),(ns[2]!,ns[3]!))
      let v ← mkAppM ``JGd_ExactWords.value #[← wordExpr w]
      unless ← isDefEq e v do throwError "leaf is not definitionally words: {e}"
      return (w,← mkEqRefl v)
  cache.modify (fun entries=>entries.insert e result)
  return result

elab "jgl_words" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_,lhs,rhs) := target.eq? | throwError "expected equality"
  let cache ← IO.mkRef ({} : Std.HashMap Expr (Words × Expr))
  let (_,hl) ← reflect cache lhs
  let (_,hr) ← reflect cache rhs
  let h ← mkEqTrans hl (← mkEqSymm hr)
  goal.assign h
  replaceMainGoal []
end AspisR1.JGl_WordProof
