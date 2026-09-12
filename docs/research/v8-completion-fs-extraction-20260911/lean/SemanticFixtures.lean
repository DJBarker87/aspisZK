import SemanticWireExecution
open AspisV8Completion.SemanticWireExecution
def p : Nat := 2147483647
def plus (a b : Nat) := (a+b)%p
def times (a b : Nat) := (a*b)%p
def ops : Arithmetic Nat where
  zero := 0
  add := plus
  sub := fun a b => (a+p-b)%p
  mul := times
  square := fun a => times a a
  sumProducts3 := fun a b => ((List.finRange 3).map (fun i => times (a i) (b i))).foldl plus 0

def minus (a b : Nat) := (a+p-b)%p
structure C where
  a : Nat
  b : Nat
structure Q where
  c : C
  d : C
def ca (x y : C) : C := ⟨plus x.a y.a, plus x.b y.b⟩
def cs (x y : C) : C := ⟨minus x.a y.a, minus x.b y.b⟩
def cm (x y : C) : C := ⟨minus (times x.a y.a) (times x.b y.b),
  plus (times x.a y.b) (times x.b y.a)⟩
def qa (x y : Q) : Q := ⟨ca x.c y.c, ca x.d y.d⟩
def qs (x y : Q) : Q := ⟨cs x.c y.c, cs x.d y.d⟩
def qm (x y : Q) : Q := ⟨ca (cm x.c y.c) (cm ⟨2,1⟩ (cm x.d y.d)),
  ca (cm x.c y.d) (cm x.d y.c)⟩
def qzero : Q := ⟨⟨0,0⟩,⟨0,0⟩⟩
def qops : Arithmetic Q where
  zero := qzero
  add := qa
  sub := qs
  mul := qm
  square := fun x => qm x x
  sumProducts3 := fun a b => ((List.finRange 3).map (fun i => qm (a i) (b i))).foldl qa qzero
def qvalue (n : Nat) : Q := ⟨⟨n%p,(p-1-n%p)%p⟩,⟨(n*13)%p,(n*n+7)%p⟩⟩

def main : IO Unit := do
  for seed in List.range 32 do
    let w : Word Nat := fun i => (i.val*i.val+seed*17+9)%p
    let coins : Fin 10 → Nat := fun i => i.val*11+seed
    let result := terminalInput ops w coins
    IO.println s!"SEMANTIC {seed} {result.1}"
    let qw : Word Q := fun i => qvalue (i.val*i.val+seed*17+9)
    let qc : Fin 10 → Q := fun i => qvalue (i.val*11+seed)
    let out := (terminalInput qops qw qc).1
    IO.println s!"SEMANTIC_Q {seed} {out.c.a} {out.c.b} {out.d.a} {out.d.b}"
