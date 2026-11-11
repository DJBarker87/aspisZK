import os, re, sys, json, random
src = sys.argv[1]; T = sys.argv[2]
cl = lambda r: set(json.load(open(f"{T}/cl_{r}.json"))["local"])
A = cl("Frozen2StartChargeProbability"); B = cl("RPz7_F3T_Numeric") - A; C = cl("TAS_FinalB") - A - B
GEN_EXT = {"Mathlib","Init","Lean","Std","FS","FS2","R0","R0C","R0P","Wide","AspisV8R15","AspisV8R17","AspisV8R19","CompPoly","AspisFormal","R1Z"}
imp = re.compile(r'^import\s+(\S+)', re.M)
local = {f[:-5] for f in os.listdir(src) if f.endswith('.lean')}
p_iv = re.compile(r'\bAeneas\b|Extracted|Extract\b|_extract|Realizes|SourceRefin|AdapterRw|RustSource|\bOp\d|Port26|Poseidon')
p_iii = re.compile(r'[Cc]heckpoint|[Cc]kpt|\btx1\b|\btx2\b|TX1|TX2|[Ss]tage[12]|SCE_Experiment|RSL\.TASB\.Runs|\bRuns\b|AccountExperiment|ARX_|ART_|ARQ_|\bresume\b|Qv[Ss]tage')
p_ii = re.compile(r'LiteralClassifier|UnifiedSampler|SelectedTranscriptParams|LiteralByteProtocol|LiteralTranscript|UnifiedDecoder|UnifiedLabels|\b33\b|\b34\b|Literal[A-Z]\w+|RecordedBinaryExperimentBin|RawCut')
def klass(m):
    txt = open(os.path.join(src, m + '.lean'), errors='replace').read()
    ims = imp.findall(txt)
    ext = [i for i in ims if i not in local and i.split('.')[0] not in GEN_EXT]
    body = re.sub(r'^import.*$', '', txt, flags=re.M)
    body = re.sub(r'/-.*?-/', '', body, flags=re.S)
    body = re.sub(r'--.*$', '', body, flags=re.M)
    if ext or p_iv.search(body): return 'iv'
    if p_iii.search(body): return 'iii'
    if p_ii.search(body): return 'ii'
    return 'i'
out = {}
for name, S in [("A_restricted_union_bound", A), ("B_numeric_minus_A", B), ("C_headline_minus_AB", C)]:
    res = {k: [] for k in ['i','ii','iii','iv']}
    for m in sorted(S): res[klass(m)].append(m)
    out[name] = res
    print(name, len(S), {k: len(v) for k, v in res.items()})
json.dump(out, open(f"{T}/classes.json","w"), indent=0)
