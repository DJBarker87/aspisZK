exec((__import__('pathlib').Path(__file__).parent/'generate-neutral.py').read_text().split("raw='PV_RunJoin_CircleRawScalar52'")[0])
p=R/'docs/research/100bit-spend-path-20261013/evidence/actual-ten-round-polynomial-run-20261019/focused-dependency-checks/selected-canonical-R72-Funs-20261019/source.lean'
s=p.read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'@\[.*?\]\s*','',s,flags=re.S)
s=s[s.index('def core.option.Option.ok_or'):]
s=s[:re.search(r'^def\s+transcript\.',s,re.M).start()]
parts=[p.strip() for p in re.split(r'(?=^def )',s,flags=re.M) if p.strip()];defs={re.match(r'def (\S+)',p)[1]:p for p in parts}
# Transform only the typed projections and constructor labels, leaving variable names unchanged.
def neutral(d):
 d=re.sub(r'\{ a, b \}', '{ fst := a, snd := b }',d)
 d=re.sub(r'\{ c0 := c, c1 \}', '{ fst := c, snd := c1 }',d)
 for a,b in [('a','fst'),('b','snd'),('c0','fst'),('c1','snd'),('x','fst'),('y','snd')]:
  d=re.sub(r'\.'+a+r'\b','.'+b,d);d=re.sub(r'\b'+a+r'\s*:=',b+' :=',d)
 return d
body='''abbrev field.M31 := U32
abbrev field.CM31 := U32 × U32
abbrev field.QM31 := field.CM31 × field.CM31
abbrev circle.SecureCirclePoint := field.QM31 × field.QM31
abbrev circle.CirclePointError := Bool
def circle.CirclePointError.SingularParameter : Bool := false
def circle.CirclePointError.ParameterInCm31Subfield : Bool := true
abbrev field.r24_canonical_mul.closure := Unit
'''
body+='\n\n'.join(neutral(d) for d in defs.values())
write('PV_RunJoin_CircleR72Raw52',['Aeneas'],body,list(defs))
carrier='''abbrev CM := U32 × U32
abbrev Q := CM × CM
abbrev Point := Q × Q
abbrev OC := AspisR72Sampler.field.CM31
abbrev OQ := AspisR72Sampler.field.QM31
abbrev OP := AspisR72Sampler.circle.SecureCirclePoint
def encCM (a : CM) : OC := ⟨a.1,a.2⟩
def decCM (a : OC) : CM := (a.a,a.b)
def encQ (a : Q) : OQ := ⟨encCM a.1,encCM a.2⟩
def decQ (a : OQ) : Q := (decCM a.c0,decCM a.c1)
def encPoint (a : Point) : OP := ⟨encQ a.1,encQ a.2⟩
def decPoint (a : OP) : Point := (decQ a.x,decQ a.y)
def encError (e : Bool) : AspisR72Sampler.circle.CirclePointError :=
  if e then .ParameterInCm31Subfield else .SingularParameter
def encOutcome (r : core.result.Result Point Bool) :
    core.result.Result OP AspisR72Sampler.circle.CirclePointError :=
  match r with | .Ok p => .Ok (encPoint p) | .Err e => .Err (encError e)
theorem cm_roundtrip (a : CM) : decCM (encCM a)=a := rfl
theorem q_roundtrip (a : Q) : decQ (encQ a)=a := rfl
theorem point_roundtrip (a : Point) : decPoint (encPoint a)=a := rfl
theorem cm_source (a : OC) : encCM (decCM a)=a := rfl
theorem q_source (a : OQ) : encQ (decQ a)=a := rfl
theorem point_source (a : OP) : encPoint (decPoint a)=a := rfl
theorem cm_a (a : CM) : (encCM a).a=a.1 := rfl
theorem cm_b (a : CM) : (encCM a).b=a.2 := rfl
theorem q_c0 (a : Q) : (encQ a).c0=encCM a.1 := rfl
theorem q_c1 (a : Q) : (encQ a).c1=encCM a.2 := rfl
'''
write('PV_RunJoin_CircleR72Carrier52',['AspisR72Sampler.Types'],carrier,re.findall(r'^(?:theorem|def) (\w+)',carrier,re.M))
(E/'r72-neutral-generation.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),functions=list(defs),method='new neutral tuple definitions; selected source unchanged'),indent=2)+'\n')
