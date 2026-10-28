import NDO_JFr_WordArithmetic
set_option autoImplicit false
namespace AspisR1.JFp_SHA256

/-- Executable mathematical SHA256, separate from the syscall/artifact port. -/
structure Reg where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat
  deriving DecidableEq

def modulus : Nat := 4294967296
def word (x : Nat) : Nat := x % modulus
def rotr (x n : Nat) : Nat := word (x / 2^n + x * 2^(32-n))
def small0 (x : Nat) : Nat := rotr x 7 ^^^ rotr x 18 ^^^ (x / 8)
def small1 (x : Nat) : Nat := rotr x 17 ^^^ rotr x 19 ^^^ (x / 1024)
def big0 (x : Nat) : Nat := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def big1 (x : Nat) : Nat := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

def advance (w : List Nat) : List Nat :=
  w.drop 1 ++ [word (small1 (w.getD 14 0) + w.getD 9 0 + small0 (w.getD 1 0) + w.getD 0 0)]

def round (s : Reg) (k w : Nat) : Reg :=
  let ch := (s.e &&& s.f) ^^^ ((s.e ^^^ 4294967295) &&& s.g)
  let maj := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
  let t1 := s.h + big1 s.e + ch + k + w
  let t2 := big0 s.a + maj
  ⟨word (t1+t2),s.a,s.b,s.c,word (s.d+t1),s.e,s.f,s.g⟩

def constants : List Nat := [
  1116352408,1899447441,3049323471,3921009573,961987163,1508970993,2453635748,2870763221,
  3624381080,310598401,607225278,1426881987,1925078388,2162078206,2614888103,3248222580,
  3835390401,4022224774,264347078,604807628,770255983,1249150122,1555081692,1996064986,
  2554220882,2821834349,2952996808,3210313671,3336571891,3584528711,113926993,338241895,
  666307205,773529912,1294757372,1396182291,1695183700,1986661051,2177026350,2456956037,
  2730485921,2820302411,3259730800,3345764771,3516065817,3600352804,4094571909,275423344,
  430227734,506948616,659060556,883997877,958139571,1322822218,1537002063,1747873779,
  1955562222,2024104815,2227730452,2361852424,2428436474,2756734187,3204031479,3329325298]

def transition (state : List Nat × Reg) (k : Nat) : List Nat × Reg :=
  (advance state.1,round state.2 k (state.1.getD 0 0))
def loop (ks w : List Nat) (s : Reg) : Reg := (ks.foldl transition (w,s)).2

def add (s t : Reg) : Reg :=
  ⟨word (s.a+t.a),word (s.b+t.b),word (s.c+t.c),word (s.d+t.d),
   word (s.e+t.e),word (s.f+t.f),word (s.g+t.g),word (s.h+t.h)⟩

def compress (s : Reg) (w : List Nat) : Reg := add s (loop constants w s)
def initial : Reg := ⟨1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225⟩
def beWord (b : List Nat) : Nat :=
  16777216*b.getD 0 0 + 65536*b.getD 1 0 + 256*b.getD 2 0 + b.getD 3 0

def words (b : List Nat) : List Nat := (List.range 16).map (fun i => beWord (b.drop (4*i)))
def pad (b : List Nat) : List Nat :=
  b ++ [128] ++ List.replicate ((119-b.length%64)%64) 0 ++
    List.ofFn (fun i : Fin 8 => (8*b.length / 256^(7-i.val)) % 256)
def blocks : Nat → List Nat → List (List Nat)
  | 0,_ => []
  | n+1,b => b.take 64 :: blocks n (b.drop 64)
def hash (b : List Nat) : Reg :=
  let padded := pad b
  (blocks (padded.length/64) padded).foldl (fun s b => compress s (words b)) initial

end AspisR1.JFp_SHA256
