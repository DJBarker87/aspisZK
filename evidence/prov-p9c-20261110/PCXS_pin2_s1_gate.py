import subprocess, json, hashlib, sys, re, os
REPO="/Users/dominic/ZK"
BASE="4bb3b3f51e16b4525f1d10336e2b0bcbbd775387"
POOLREF="b936275465600469312d1f058cdc91ea2a11f3dc"
PIN, HEAD = sys.argv[1], sys.argv[2]
OUT=sys.argv[3]
def g(*a, raw=False):
    r=subprocess.run(["git","-C",REPO]+list(a),capture_output=True,check=True)
    return r.stdout if raw else r.stdout.decode()
def full(c): return g("rev-parse",c).strip()
PIN,HEAD=full(PIN),full(HEAD)
W1_COMMITS=[full("43919c0a9f2"),full("271869c946d")]
W1_FILES={"programs/r1-cost-probe/src/pool_v1/pair_forest_semantic_terminal.rs","crates/aspis-r1-cost-probe/src/pool_v1/pair_forest_semantic_terminal.rs",
 "programs/r1-cost-probe/src/r1_pool_adapter.rs","programs/r1-cost-probe/src/pool_route.rs",
 "programs/r1-cost-probe/src/close_checkpoint_tests.rs","programs/r1-cost-probe/src/r1_checkpoint_tests.rs"}
# W1 named files exactly as in git diff 4bb3b3f 271869c946d
W1_FILES=set(g("diff","--name-only",BASE,W1_COMMITS[1]).split())
Z4_SRC={"probe.rs","r1p_lib.rs","z9.rs","z9b.rs","z9c.rs","z9d.rs","z9e.rs"}
Z4="docs/research/v8-r0-zk-20261009/z4/"
def cls(p, commit_kind):
    if commit_kind=="tools":
        if p.startswith(("evidence/","scripts/","tools/")): return "tools"
        return "NOT_NAMED"
    if p in W1_FILES and commit_kind=="W1": return "W1"
    if commit_kind=="W1": return "NOT_NAMED"
    # Stream B commit
    if p.startswith("crates/"): return "STREAM_B_SHIPPED"
    if p.startswith("programs/r1-cost-probe/"): return "STREAM_B_SHIPPED"
    if p.startswith("programs/aspis-upload/"): return "STREAM_B_SHIPPED"
    if p.startswith("programs/aspis-pool/"): return "POOL_LINE"
    if p=="Cargo.lock": return "STREAM_B_SHIPPED"
    if p=="Cargo.toml": return "STREAM_B_SHIPPED_WORKSPACE_MANIFEST_FLAG"
    if p.startswith(Z4):
        r=p[len(Z4):]
        if r in Z4_SRC: return "STREAM_B_SHIPPED"
        if r.startswith("orig/") or r=="r1p_tests.rs": return "STREAM_B_TEST"
        return "NOT_NAMED"
    if p.startswith("docs/research/"): return "DOCS_NOT_SHIPPED"
    return "NOT_NAMED"
def changes(a,b):
    out=[]
    for l in g("diff-tree","-r","--no-commit-id","--name-status","--no-renames",a,b).splitlines():
        s,p=l.split("\t",1); out.append((s,p))
    return out
commits=[("43919c0a9f2","W1"),("271869c946d","W1"),("c7593d23fdc","STREAM_B"),("d7142292c48","tools")]
per_commit={}
notnamed=[]
for c,k in commits:
    cf=full(c); par=g("rev-parse",cf+"^").strip()
    kind={"W1":"W1","STREAM_B":"B","tools":"tools"}[k]
    rows=[]
    for s,p in changes(par,cf):
        c_=cls(p,"W1" if kind=="W1" else kind)
        rows.append({"status":s,"path":p,"class":c_})
        if c_=="NOT_NAMED": notnamed.append({"commit":c,"path":p})
    per_commit[c]={"parent":par,"n":len(rows),"by_class":{},"paths":rows}
    for r in rows: per_commit[c]["by_class"][r["class"]]=per_commit[c]["by_class"].get(r["class"],0)+1
# cumulative base..head
cum=changes(BASE,HEAD)
cum_ship=[(s,p) for s,p in cum if p.startswith(("crates/","programs/","Cargo.lock","Cargo.toml","tools/",".cargo/","rust-toolchain"))
          or re.search(r"(^|/)(Cargo\.toml|Cargo\.lock|rust-toolchain[^/]*|build\.rs)$",p)]
# aspis-pool per-file vs b936275
pool_t_pin=g("rev-parse",PIN+":programs/aspis-pool").strip()
pool_t_ref=g("rev-parse",POOLREF+":programs/aspis-pool").strip()
pool_t_head=g("rev-parse",HEAD+":programs/aspis-pool").strip()
def tree(c,d): 
    r={}
    for l in g("ls-tree","-r",c,d).splitlines():
        m,t,sha,p=re.match(r"(\d+) (\w+) (\w+)\t(.*)",l).groups(); r[p]=(m,sha)
    return r
tp,tr=tree(PIN,"programs/aspis-pool"),tree(POOLREF,"programs/aspis-pool")
pool_files=[{"path":p,"in_pin":p in tp,"in_b936275":p in tr,"equal":tp.get(p)==tr.get(p)} for p in sorted(set(tp)|set(tr))]
pool_diff=[f for f in pool_files if not f["equal"]]
# sha256 listings for build-input scopes
def sha_of(c,p):
    try: return hashlib.sha256(g("cat-file","blob",f"{c}:{p}",raw=True)).hexdigest()
    except subprocess.CalledProcessError: return None
scope_re=re.compile(r"^(crates/|programs/|tools/|\.cargo/|Cargo\.lock$|Cargo\.toml$)|(^|/)(Cargo\.toml|Cargo\.lock|rust-toolchain[^/]*|build\.rs)$")
def lst(c): return {p for p in g("ls-tree","-r","--name-only",c).splitlines() if scope_re.search(p)}
bs,ps,hs=lst(BASE),lst(PIN),lst(HEAD)
allp=sorted(bs|ps|hs)
files=[]
import collections
for p in allp:
    sb,sp,sh=sha_of(BASE,p),sha_of(PIN,p),sha_of(HEAD,p)
    files.append({"path":p,"sha256_4bb3b3f":sb,"sha256_pin":sp,"sha256_head":sh,"changed_pin":sb!=sp,"changed_head":sb!=sh})
changed_in_scope=[f["path"] for f in files if f["changed_head"]]
# tools commit shipped-path check
tools_ship=[r for r in per_commit["d7142292c48"]["paths"] if r["class"]!="tools"]
# pin->head diff touches only tools?
ph=changes(PIN,HEAD); ph_non=[p for s,p in ph if not p.startswith(("evidence/","scripts/","tools/"))]
# changed-in-scope paths not classified as expected: any in scope at head vs base must be explained by a class
expl={}
for c,v in per_commit.items():
    for r in v["paths"]: expl.setdefault(r["path"],set()).add(r["class"])
unexpl=[p for p in changed_in_scope if p not in expl]
res={"base":BASE,"pin":PIN,"head":HEAD,"pool_ref":POOLREF,
 "counts":{"cumulative_changed_paths_base_to_head":len(cum),"cumulative_changed_in_build_scope":len(changed_in_scope),
   "scope_files_listed":len(files),"notnamed":len(notnamed),"pool_files_differing":len(pool_diff),
   "per_commit":{c:v["n"] for c,v in per_commit.items()}},
 "NOT_NAMED":notnamed,
 "flags":{"root_Cargo_toml_workspace_member_added":"programs/aspis-upload (class STREAM_B_SHIPPED_WORKSPACE_MANIFEST_FLAG; not literally in the named shipped list; lead to confirm)"},
 "pool_line":{"tree_pin":pool_t_pin,"tree_head":pool_t_head,"tree_b936275":pool_t_ref,"tree_equal_pin":pool_t_pin==pool_t_ref,"files_compared":len(pool_files),"differing":pool_diff,
    "note":"c7593d23fdc itself shows changes under programs/aspis-pool versus its parent 271869c946d (parent differed from b936275); versus b936275 the tree is identical"},
 "tools_commit_non_tools_paths":tools_ship,"pin_to_head_non_tools_paths":ph_non,
 "build_scope_changed_without_commit_class":unexpl,
 "per_commit":per_commit,"classes_overall":{},
 "files":files}
for v in per_commit.values():
    for k,n in v["by_class"].items(): res["classes_overall"][k]=res["classes_overall"].get(k,0)+n
json.dump(res,open(OUT+".json","w"),indent=1)
# md
L=[]
L.append(f"# PIN2 artefact gate (S1)\n\nbase {BASE}\npin  {PIN}\nhead {HEAD}\n")
L.append("## Counts\n")
L.append(f"- NOT_NAMED paths: {len(notnamed)}")
L.append(f"- programs/aspis-pool: pin tree {pool_t_pin} vs b936275 tree {pool_t_ref}: equal={pool_t_pin==pool_t_ref}; files compared {len(pool_files)}, differing {len(pool_diff)}")
L.append(f"- cumulative changed paths 4bb3b3f..head (whole tree): {len(cum)}; changed within build scope: {len(changed_in_scope)}; build-scope files hashed: {len(files)}")
for c,v in per_commit.items(): L.append(f"- {c}: {v['n']} paths, classes {v['by_class']}")
L.append(f"- tools commit paths outside evidence/scripts/tools: {len(tools_ship)}; pin..head paths outside evidence/scripts/tools: {len(ph_non)}")
L.append(f"- build-scope changes not explained by a per-commit class: {len(unexpl)}")
L.append("\n## Flag\nRoot Cargo.toml changes by one line (workspace member programs/aspis-upload) and Cargo.lock adds package aspis-upload (deps solana-program, solana-sdk-ids only). Classified STREAM_B_SHIPPED_WORKSPACE_MANIFEST_FLAG because Cargo.toml is not literally in the named shipped set; lead to confirm.")
L.append("\n## Changed build-scope paths (4bb3b3f..head)\n")
for p in changed_in_scope: L.append(f"- {p}")
open(OUT+".md","w").write("\n".join(L)+"\n")
print(json.dumps(res["counts"]),res["classes_overall"],"pool_equal",pool_t_pin==pool_t_ref,"unexpl",unexpl,"tools_non",tools_ship,ph_non)
