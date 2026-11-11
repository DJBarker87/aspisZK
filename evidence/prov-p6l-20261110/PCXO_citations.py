#!/usr/bin/env python3
"""PCXO_citations.py (P6l item C): re-point the 18 source-citation differences of evidence/prov-p5h-20261110/PCWR_SOURCE_SHA_AUDIT.json to the l187_plan.json source and compare textually.

Usage (from the worktree root):  python3 -I evidence/prov-p6l-20261110/PCXO_citations.py [--ref research] [--fetch]
  --fetch   read the module entries from the host by ssh (read-only, one short remote script, only the listed modules; the plan file is never copied) and write
            evidence/prov-p6l-20261110/PCXO_PLAN_ENTRIES.json; without --fetch that cache is used.
Reads committed files only through `git show <ref>:<path>`. 0 Lean, 0 extraction, 0 host scopes. Writes PCXO_CITATIONS.json.
"""
import json, re, subprocess, sys, hashlib, argparse, collections
sys.dont_write_bytecode = True
ap = argparse.ArgumentParser()
ap.add_argument('--ref', default='research'); ap.add_argument('--fetch', action='store_true')
ap.add_argument('--outdir', default='evidence/prov-p6l-20261110')
ap.add_argument('--extra-modules', default='NFY_Part042,NJT_ClaimsRef_Funs,NEG_PushActual.Funs,AspisR1SelectedMaskProbe.Funs', help='further modules whose plan entry is cached for the parse_blocks audit (PCXO_recount.py)')
args = ap.parse_args()
REF = subprocess.run(['git', 'rev-parse', args.ref], capture_output=True, check=True).stdout.decode().strip()
HOST = 'dombarker@100.108.41.90'
PLAN = '/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/l187_plan.json'


def blob(p):
    r = subprocess.run(['git', 'show', REF + ':' + p], capture_output=True)
    return r.stdout if r.returncode == 0 else None


AUD = json.loads(blob('evidence/prov-p5h-20261110/PCWR_SOURCE_SHA_AUDIT.json'))
DIFFS = AUD['citations_differing_from_plan']
assert len(DIFFS) == 18, len(DIFFS)
modules = sorted({d['module'] for d in DIFFS} | set(args.extra_modules.split(',')))
CACHE = args.outdir + '/PCXO_PLAN_ENTRIES.json'
if args.fetch:
    remote = ('import json,sys\nmods=json.load(sys.stdin)\nd=json.load(open(%r))\np=d["plan"]\n'
              'print(json.dumps({"order_len":len(d["order"]),"plan_len":len(p),"entries":{m:(p.get(m) and {k:p[m][k] for k in ("module","src_rel","source","label","producing_attempt")}) for m in mods}}))\n') % PLAN
    r = subprocess.run(['ssh', '-o', 'ConnectTimeout=20', '-o', 'ServerAliveInterval=15', HOST, 'timeout 60 python3 -c %s' % json.dumps(remote).replace('"', '\\"').join(['"', '"']) if False else 'timeout 60 python3 -c ' + subprocess.list2cmdline([remote])],
                       input=json.dumps(modules).encode(), capture_output=True, timeout=90)
    if r.returncode != 0: sys.exit('ssh failed: ' + r.stderr.decode()[:400])
    out = json.loads(r.stdout.decode())
    out.update(plan_file=PLAN, host=HOST, note='read-only; module -> source path and sha256 entries only; the plan file was not copied')
    json.dump(out, open(CACHE, 'w'), indent=1); open(CACHE, 'a').write('\n')
PLANE = json.load(open(CACHE))

# ---- declaration blocks (parse_blocks of the fixed generator PCWP_: peels import lines too) -> {name: normalised text}
exec_ns = {}
src_gen = blob('evidence/prov-p5f-20261110/PCWP_gen_equalities.py').decode()
KW = r'(?:def|abbrev|structure|inductive|impl_def|opaque|axiom|theorem|instance|class)'


def uncomment(s):
    out = []; i = 0; depth = 0; string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out += [' ', ' ']; i += 2
            elif s.startswith('-/', i): depth -= 1; out += [' ', ' ']; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s): out += [' ', ' ']; i += 2
            elif s[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i): depth = 1; out += [' ', ' ']; i += 2
        elif s.startswith('--', i):
            end = s.find('\n', i); end = len(s) if end < 0 else end; out.extend(' ' * (end - i)); i = end
        elif s[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(s[i]); i += 1
    return ''.join(out)


def split_attr(clean):
    i = 0; attrs = []
    while True:
        m = re.match(r'\s*@\[', clean[i:])
        if not m: break
        j = i + m.end(); depth = 1; k = j
        while k < len(clean) and depth:
            if clean[k] == '[': depth += 1
            elif clean[k] == ']': depth -= 1
            k += 1
        attrs.append(clean[j:k - 1]); i = k
    return attrs, clean[i:]


def decl_blocks(text):
    """declarations of the file as (name, code text without comments, whitespace-normalised, attributes included), in file order; fixed peel (PCWP_)"""
    clean = uncomment(text)
    raw_blocks = re.split(r'\n[ \t]*\n', text)
    pos = 0; out = []
    for rb in raw_blocks:
        start = text.find(rb, pos); end = start + len(rb); pos = end
        while True:
            m0 = re.match(r'[ \t]*(?:import|namespace|section|open|set_option|variable|universe|noncomputable section)\b[^\n]*\n', rb)
            if not m0 or '\n' not in rb[m0.end():] and not rb[m0.end():].strip(): break
            start += m0.end(); rb = rb[m0.end():]
        cb = clean[start:end]
        attrs, rest = split_attr(cb)
        m = re.match(r'\s*((?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(' + KW + r')\s+(?:\([^)]*\)\s*)?([^\s({:\[]+)', rest)
        if m and re.match(r'\s*(?:/--|@\[|(?:noncomputable|private|protected|partial|unsafe|nonrec|' + KW[3:-1] + r')\b)', rb) or (m and rb.lstrip().startswith(('/--', '@['))):
            out.append((m.group(3), ' '.join(cb.split())))
    return out


def sha(b): return hashlib.sha256(b).hexdigest()


def find_by_sha(sha256, basenames):
    """cited sha without a path (PCVB_STATUS blob citations): hash the repository files with the module's basename(s) at REF"""
    ls = subprocess.run(['git', 'ls-tree', '-r', '--name-only', REF], capture_output=True, check=True).stdout.decode().split('\n')
    return ls


LS = None
def candidates(bases):
    global LS
    if LS is None: LS = subprocess.run(['git', 'ls-tree', '-r', '--name-only', REF], capture_output=True, check=True).stdout.decode().split('\n')
    bs = set(bases)
    return [f for f in LS if f.split('/')[-1] in bs]


def compare(plan_text, cited_text):
    pb = decl_blocks(plan_text); cb = decl_blocks(cited_text)
    pd = collections.OrderedDict(); cd = collections.OrderedDict()
    dup_p = collections.Counter(n for n, _ in pb); dup_c = collections.Counter(n for n, _ in cb)
    for n, t in pb: pd.setdefault(n, []).append(t)
    for n, t in cb: cd.setdefault(n, []).append(t)
    only_p = sorted(set(pd) - set(cd)); only_c = sorted(set(cd) - set(pd))
    differ = sorted(n for n in set(pd) & set(cd) if pd[n] != cd[n])
    same = sorted(n for n in set(pd) & set(cd) if pd[n] == cd[n])
    return dict(plan_declarations=len(pb), cited_declarations=len(cb), identical_declarations=len(same), differing_declarations=differ, only_in_plan_source=only_p, only_in_cited_source=only_c,
                duplicate_names_plan=sorted(n for n, c in dup_p.items() if c > 1), duplicate_names_cited=sorted(n for n, c in dup_c.items() if c > 1),
                whole_file_identical=(plan_text == cited_text))


records = []
for d in DIFFS:
    m = d['module']
    pe = PLANE['entries'].get(m)
    rec = dict(module=m, kind=d['kind'], cited_path=d.get('cited_path'), cited_source_path=d.get('cited_source_path'), cited_sha256=d['cited_sha256'], audit_plan_path=d['plan_path'], audit_plan_sha256=d['plan_sha256'],
               audit_plan_label=d['plan_label'], files_citing=d.get('files'), jobs_citing=d.get('jobs'))
    if not pe: rec['status'] = 'PLAN_ENTRY_MISSING'; records.append(rec); continue
    rec['l187_plan'] = dict(path=pe['source']['path'], sha256=pe['source']['sha256'], label=pe['label'], src_rel=pe['src_rel'], producing_attempt=pe['producing_attempt'])
    rec['plan_equals_audit_plan'] = (pe['source']['sha256'] == d['plan_sha256'])
    ppath = pe['source']['path']
    pb_ = blob(ppath) or blob(ppath.replace('docs/research/100bit-spend-path-20261013/', ''))
    rec['plan_source_in_repo'] = pb_ is not None
    if pb_ is None: rec['status'] = 'PLAN_SOURCE_NOT_IN_REPO'; records.append(rec); continue
    rec['plan_source_sha256_recomputed'] = sha(pb_); rec['plan_source_sha_matches_plan_entry'] = (sha(pb_) == pe['source']['sha256'])
    # the cited text
    ct = None; how = None
    cp = d.get('cited_path'); csp = d.get('cited_source_path')
    for pth, tag in ((cp, 'cited_path'), (csp, 'cited_source_path')):
        if pth and ct is None:
            b = blob(pth) or blob('docs/research/100bit-spend-path-20261013/' + pth) or blob(pth.replace('docs/research/100bit-spend-path-20261013/', ''))
            if b is not None and (sha(b) == d['cited_sha256'] or tag == 'cited_path' and d['kind'] in ('path_cite', 'generator_input_copy_sha')):
                ct = b; how = tag + ' ' + pth + (' (sha256 equals the cited sha)' if sha(b) == d['cited_sha256'] else ' (path cite; sha256 differs from the recorded cite: %s)' % sha(b)[:12])
    if ct is None and d['kind'] == 'sha_cite':
        # PCVB_STATUS.json cites the sha256 of the PROVING file (files[].sha256), not of a gate source: re-point to the plan source and check that every theorem right-hand side of the proving file is a declaration of the plan source
        st = json.loads(blob('evidence/prov-p3b-20261109/PCVB_STATUS.json'))
        fl = [x for x in st['files'] if x['sha256'] == d['cited_sha256'] and x['module'] == m]
        if fl:
            pf = 'evidence/prov-p3b-20261109/' + fl[0]['file']
            b = blob(pf)
            rec['cited_is'] = 'sha256 of the proving file %s (PCVB_STATUS files[].sha256, receipt %s), not of a gate source: the citation entry is not a gate-source citation' % (fl[0]['file'], fl[0]['receipt'])
            rec['proving_file_in_repo'] = pf if b is not None else None
            rec['proving_file_sha_matches'] = (b is not None and sha(b) == d['cited_sha256'])
            nsx = re.findall(r'(?m)^namespace\s+(\S+)', pt_text := pb_.decode('utf-8', 'replace'))
            names = {n for n, _ in decl_blocks(pt_text)}
            fullnames = {n for n in names} | {ns + '.' + n for ns in nsx for n in names}
            thm = re.findall(r'(?m)^theorem\s+(\S+)\s*:\s*@(\S+)\s*=\s*@(\S+?)\s*:=', b.decode('utf-8', 'replace')) if b is not None else []
            miss = sorted({r_ for _, _, r_ in thm if r_ not in fullnames and not any(r_ == ns + '.' + n for ns in nsx for n in names)})
            rec['proving_file_check'] = dict(equality_theorems=len(thm), gate_names_resolving_to_plan_source_declarations=len({r_ for _, _, r_ in thm}) - len(miss), gate_names_not_declared_in_plan_source=miss,
                                              plan_source_namespaces=nsx, plan_declarations=len(names))
            rec['status'] = 'CITATION_IS_PROVING_FILE_SHA' + ('' if not miss else '_WITH_UNRESOLVED_NAMES')
            records.append(rec); continue
    if ct is None:    # sha-only citations: search same-basename files for the cited sha
        bases = {ppath.split('/')[-1], 'gate_' + m.replace('.', '_') + '.lean', m.split('.')[-1] + '.lean'}
        for f in candidates(bases):
            b = blob(f)
            if b is not None and sha(b) == d['cited_sha256']: ct = b; how = 'found by sha256 among same-basename files: ' + f; break
    if ct is None:
        rec['status'] = 'CITED_SOURCE_NOT_RECOVERABLE'; rec['note'] = 'the cited sha256 matches no repository file with a related basename at %s' % REF[:12]; records.append(rec); continue
    rec['cited_source_found'] = how; rec['cited_source_sha256_recomputed'] = sha(ct)
    pt = pb_.decode('utf-8', 'replace'); ctt = ct.decode('utf-8', 'replace')
    cmp_ = compare(pt, ctt)
    rec['comparison'] = cmp_
    rec['status'] = 'IDENTICAL_DECLARATIONS' if (not cmp_['differing_declarations'] and not cmp_['only_in_plan_source'] and not cmp_['only_in_cited_source'] and cmp_['plan_declarations'] == cmp_['cited_declarations']) else 'DECLARATIONS_DIFFER'
    records.append(rec)

res = dict(schema='PCXO_CITATIONS/1', target_established=False, research_ref=REF, authority=PLAN + ' on host ' + HOST + ' (read-only ssh; module entries only, cached in PCXO_PLAN_ENTRIES.json)',
           plan_size=dict(order=PLANE['order_len'], plan=PLANE['plan_len']),
           statement='A citation difference is not a proof error: statements are against compiled gate constants. Each record re-points the citation to the l187_plan.json source and compares the gate declarations of the plan source with those of the cited source (declaration count, per-declaration text equality after comment removal and whitespace normalisation, using the declaration split of the fixed generator parse_blocks, PCWP_).',
           counts=dict(records=len(records), by_status=dict(collections.Counter(r['status'] for r in records))),
           declarations_whose_text_differs=[dict(module=r['module'], cited=r.get('cited_path') or r.get('cited_source_found'), declarations=r['comparison']['differing_declarations'], only_in_plan_source=r['comparison']['only_in_plan_source'], only_in_cited_source=r['comparison']['only_in_cited_source'])
                                           for r in records if r.get('comparison') and r['status'] == 'DECLARATIONS_DIFFER'],
           records=records)
json.dump(res, open(args.outdir + '/PCXO_CITATIONS.json', 'w'), indent=1); open(args.outdir + '/PCXO_CITATIONS.json', 'a').write('\n')
print(json.dumps(res['counts']))
for r in records:
    c = r.get('comparison')
    print(r['module'][:34].ljust(34), r['status'].ljust(24), (('plan %d cited %d identical %d differ %d onlyP %d onlyC %d' % (c['plan_declarations'], c['cited_declarations'], c['identical_declarations'], len(c['differing_declarations']), len(c['only_in_plan_source']), len(c['only_in_cited_source']))) if c else r.get('note', '')))
