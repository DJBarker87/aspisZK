#!/usr/bin/env python3
"""Fail-closed evidence checker for B-y rows. Does not prove Lean statements."""
import argparse
from collections import Counter
import hashlib
import json
import lzma
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ROOT / 'design/PRIVACY-FN-LEDGER-20261108.json'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FACT_PREFIX = {
    'documented_semantics': ('PV_THR2_IntrinsicSemantics_', 'PV_STX2_IntrinsicSemantics_'),
    'operator_semantics': ('PV_THR2_OperatorSemantics_',),
    'typed_representation': ('PV_THR2_TypedRepresentation_',),
}
FACT_EXACT = {'FreshAllocationValidity': "FreshAllocationValidity'",
              'ClientLayout': 'PV_OWN2_ClientLayout', 'PinnedConfig': 'PV_STX2_PinnedConfig'}

class Invalid(ValueError):
    pass

def require(ok, message):
    if not ok:
        raise Invalid(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def git(*args):
    p = subprocess.run(['git', *args], cwd=ROOT, capture_output=True)
    require(p.returncode == 0, 'git ' + ' '.join(args[:2]) + ': ' + p.stderr.decode().strip())
    return p.stdout

def read_ref(ref):
    """Always read historical evidence at a pinned git revision, never branch HEAD."""
    require(re.fullmatch(r'[0-9a-f]{40}', ref.get('revision', '')), 'full revision required')
    raw = git('show', ref['revision'] + ':' + ref['path'])
    require(sha(raw) == ref.get('sha256'), 'artifact SHA-256 mismatch: ' + ref['path'])
    return lzma.decompress(raw) if ref['path'].endswith('.xz') else raw

def strip_comments(text):
    # Retain strings; remove nested Lean block comments and line comments.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            i = text.find('\n', i)
            if i < 0:
                break
        else:
            out.append(text[i]); i += 1
    require(depth == 0, 'unterminated Lean comment')
    return ''.join(out)

def declared_theorems(source):
    scopes, result = [], set()
    for match in re.finditer(r'^\s*(namespace\s+([^\s]+)|section(?:\s+[^\s]+)?|end(?:\s+[^\s]+)?|(?:protected\s+)?theorem\s+([^\s({:]+))', source, re.M):
        token = match[1]
        if token.startswith('namespace'):
            scopes.append(match[2])
        elif token.startswith('section'):
            scopes.append('')
        elif token.startswith('end'):
            if scopes: scopes.pop()
        elif match[3]:
            result.add('.'.join([x for x in scopes if x] + [match[3]]))
    return result


def printed_binders(text, theorem):
    """Read named leading binders in #print output; reject unsupported syntax.

    Return an exhaustive lexical binder list, including data parameters. This
    is deliberately stricter than Lean; anonymous arrow premises are refused.
    """
    text = strip_comments(text)
    match = re.search(r'\btheorem\s+' + re.escape(theorem) + r'(?:\.\{[^}]*\})?\s*', text)
    require(match is not None, 'printed statement does not name theorem')
    signature = text[match.end():].split(':=', 1)[0].strip()
    binders = []
    def consume(s):
        while s and s[0] in '({[':
            stack, quote, end = [], False, None
            for i, char in enumerate(s):
                if char == '"':
                    quote = not quote
                if quote:
                    continue
                if char in '({[':
                    stack.append(char)
                elif char in ')}]':
                    require(stack and '({['[')}]'.index(char)] == stack.pop(), 'unbalanced printed binder')
                    if not stack:
                        end = i + 1; break
            require(end is not None, 'unterminated printed binder')
            binder = s[:end]
            require(':' in binder, 'unnamed/typeclass binder requires explicit inventory name')
            binders.append(binder)
            s = s[end:].lstrip()
        return s
    signature = consume(signature)
    require(signature.startswith(':'), 'unsupported declaration statement format')
    signature = signature[1:].strip()
    while signature.startswith('∀') or signature.startswith('forall '):
        signature = signature[1:].strip() if signature.startswith('∀') else signature[7:].strip()
        before = len(binders)
        signature = consume(signature)
        require(len(binders) > before and signature.startswith(','), 'unnamed forall binder is unsupported')
        signature = signature[1:].strip()
    # A contract conclusion should be one named proposition applied to parameters.
    require('→' not in signature and ' -> ' not in signature, 'anonymous proposition premises are not inventoried')
    return binders, signature

def check_statement(closure, row, rows):
    raw = read_ref(closure['statement'])
    artifact = json.loads(raw)
    require(artifact.get('format') == 'pv-ledger-printed-statement-v1', 'expected verbatim printed statement artifact')
    text = artifact['printed_statement']
    require(sha(text.encode()) == artifact.get('printed_statement_sha256'), 'printed text hash mismatch')
    require(artifact.get('theorem') == closure['theorem'], 'statement theorem mismatch')
    require(artifact.get('source_sha256') == closure['source']['sha256'], 'statement/source association mismatch')
    binders, conclusion = printed_binders(text, closure['theorem'])
    inventory = artifact['binders']
    require([x['verbatim'] for x in inventory] == binders, 'printed binder inventory is not exhaustive/in order')
    if row['kind'] == 'BODY':
        require(conclusion.startswith(row['contract']['lean_post']) or conclusion.startswith(row['contract']['lean_contract']),
                'theorem conclusion is not this row Post/Contract')
    has_pre = False
    for item in inventory:
        binder = item['verbatim']
        typ = binder[1:-1].split(':', 1)[1].strip()
        role = item.get('role')
        if role == 'parameter':
            require(not re.search(r'\b(Prop|Pre|Post|Contract|Cases|Shape|Proof)\b', typ), 'proposition-bearing parameter needs hypothesis audit')
            require(item.get('type_checked_non_proposition') is True, 'parameter classification receipt absent')
            continue
        require(role == 'hypothesis', 'unclassified printed binder')
        category = item.get('category')
        if category == 'Pre':
            require(row['kind']=='BODY' and typ.startswith(row['contract']['lean_pre'] + ' '), 'wrong row Pre')
            has_pre = True
        elif category in FACT_PREFIX:
            fact = item.get('fact', '')
            require(any(fact.startswith(p) for p in FACT_PREFIX[category]), 'fact outside B-y category')
            require(typ.startswith(fact) and (len(typ)==len(fact) or typ[len(fact)] in ' .('), 'hypothesis not the named fact')
            require(item.get('ruling') in {'thread-4','thread-6','thread-7','thread-13','thread-15','slice-6'}, 'fact ruling absent')
        elif category in FACT_EXACT:
            require(item.get('fact') == FACT_EXACT[category], 'fact outside inventory')
            require(typ.startswith(item['fact']), 'hypothesis not the allowed fact')
        elif category == 'leaf_returned_case':
            child = rows.get(item.get('leaf'))
            require(child is not None and child['kind']=='LEAF', 'returned-case hypothesis is not LEAF')
            require(child['id'] in row['callees'] or child['id']==row['id'], 'leaf case not at actual child edge')
            require(item.get('request') in typ and '.answer' in typ and '.returned' in typ,
                    'leaf returned case must quote actual request/answer in printed type')
        else:
            raise Invalid('hypothesis outside B-y inventory: ' + binder[:120])
        # A permitted label must never hide a BODY contract premise.
        for child in rows.values():
            if child['kind']=='BODY':
                require(child['contract']['lean_contract'] not in typ, 'BODY contract remains a hypothesis')
    require(row['kind']=='LEAF' or has_pre, 'BODY theorem lacks its own named Pre')
    return artifact

def check_closed(row, rows):
    c = row.get('closure')
    require(isinstance(c, dict), 'CLOSED row has no closure receipt')
    rev, branch = c['source']['revision'], c['branch']
    if row['kind']=='BODY':
        require(c['theorem']==row['contract']['lean_theorem'], 'CLOSED theorem differs from expected contract theorem')
    git('merge-base', '--is-ancestor', rev, branch)
    source = strip_comments(read_ref(c['source']).decode())
    require(c['theorem'] in declared_theorems(source), 'named theorem absent at branch revision')
    require(c.get('boundary') == ('CALL_ENTRY_TO_RETURN' if row['kind']=='BODY' and row['emitted_kind']!='CompositionRoot' else
                                'ORIGINAL_ENTRY_TO_OWNINIT_CASE_SPLIT' if row['emitted_kind']=='CompositionRoot' else 'LEAF_FULL_REPLY'),
            'wrong theorem entry/return boundary')
    check_statement(c, row, rows)
    audit = json.loads(read_ref(c['raw_audit']))
    require(audit.get('mode')=='raw_walk', 'summary-based audit is not raw')
    require(audit.get('source_revision')==rev, 'raw audit revision differs from theorem source')
    require(audit.get('complete') is True and audit.get('unresolved_constants') == 0, 'incomplete raw audit')
    require(audit.get('failures') == [] and audit.get('standard_axioms_only') is True, 'raw audit failed')
    require(audit.get('roots_requested') == audit.get('roots_completed') and audit.get('roots_completed',0)>0, 'raw audit omitted roots')
    roots = [x for x in audit['roots'] if x['root']==c['theorem']]
    require(len(roots)==1, 'theorem missing/duplicated in raw audit')
    require(roots[0].get('source_sha256')==c['source']['sha256'], 'raw audit root/source hash mismatch')
    require(set(roots[0]['walked_axioms']) <= STANDARD_AXIOMS and roots[0].get('standard_axioms_only') is True,
            'raw root uses nonstandard axioms')
    require(roots[0].get('equal') is True, 'raw/summary disagreement')
    require(audit.get('augmented_summary_mismatches',[]) == [], 'raw augmented summary mismatch')
    require(c.get('raw_audit_source_sha256') == c['source']['sha256'], 'raw audit source association absent')
    applications = c.get('callee_instantiations',[])
    body_children = {x for x in row['callees'] if rows[x]['kind']=='BODY'}
    require({x['row'] for x in applications} == body_children, 'BODY callee instantiations incomplete')
    for app in applications:
        child = rows[app['row']]
        require(child['status']=='CLOSED', 'BODY callee is not CLOSED: '+child['id'])
        require(app['theorem']==child['closure']['theorem'], 'wrong callee contract theorem')
        require(app.get('actual_arguments') and app.get('entry_state'), 'actual callee arguments/state missing')
        require(app.get('source_excerpt') in source and app['theorem'] in app['source_excerpt'], 'callee application absent from theorem source')
    require(c.get('all_reply_branches')==['returned','failure','divergence','pending'], 'reply branches incomplete')
    require(c.get('frame_proved_by_shape') is True, 'frame evidence absent')

def validate(data):
    errors = []
    try:
        if 'enumeration_artifact' in data:
            raw = (ROOT/data['enumeration_artifact']).read_bytes()
            require(sha(raw)==data['enumeration_sha256'], 'enumeration hash mismatch')
            enum = json.loads(raw)
            require(data['source_pins']==enum['source_pins'], 'source pins differ from enumeration')
            actual = {r['id']:r for r in data['rows']}
            require(set(actual)=={r['id'] for r in enum['rows']}, 'ledger dropped/added enumeration rows')
            for r in enum['rows']:
                for field in ['emitted_id','source_name','path','kind','emitted_kind','callees','call_sites','source']:
                    require(actual[r['id']][field]==r[field], 'enumeration drift: '+r['id']+' '+field)
            for pin in data['source_pins']:
                raw = git('show',pin['revision']+':'+pin['artifact'])
                if pin['artifact'].endswith('.xz'): raw=lzma.decompress(raw)
                require(sha(raw)==pin['sha256'], 'source input hash mismatch: '+pin['artifact'])
    except (Invalid, KeyError, OSError, ValueError) as exc:
        errors.append(str(exc))
    rows = {}
    for row in data.get('rows',[]):
        if row.get('id') in rows:
            errors.append('duplicate row '+str(row.get('id')))
        rows[row.get('id')] = row
    for row in data.get('rows',[]):
        rid = row.get('id','<missing id>')
        try:
            require(row.get('path') in {'slice','thread'}, 'unknown path')
            require(row.get('kind') in {'BODY','LEAF'}, 'unknown kind')
            require(row.get('status') in {'OPEN','PARTIAL','CLOSED'}, 'unknown status')
            require(all(x in rows for x in row['callees']), 'missing callee row')
            require(all(c['row'] in row['callees'] for c in row['call_sites']), 'call edge missing')
            require(row.get('source_name') and row.get('disposition'), 'source identity/disposition absent')
            if row['kind']=='BODY':
                con = row['contract']
                require(all(con.get(k) for k in ['pre','post','frame','lean_pre','lean_post','lean_contract','lean_theorem','parameters']), 'contract incomplete')
                require(set(con['reply_branches'])=={'returned','failure','divergence','pending'}, 'draft omits reply branch')
            else:
                require(row.get('leaf',{}).get('named_fact') or row.get('leaf',{}).get('named_child'), 'unnamed leaf')
            if row['status']=='PARTIAL':
                require(row.get('evidence') and row.get('missing'), 'PARTIAL lacks evidence/gap')
            for ev in row.get('evidence',[]):
                raw = (ROOT/ev['statement_artifact']).read_bytes()
                require(sha(raw)==ev['statement_sha256'], 'local statement artifact changed')
                require(ev['theorem'].rsplit('.',1)[-1] in raw.decode(), 'statement does not name evidence theorem')
                require(git('cat-file','-e',ev['revision']+':'+ev['source']) == b'', 'candidate source absent')
            if row['status']=='CLOSED':
                check_closed(row,rows)
        except (Invalid, KeyError, TypeError, OSError, ValueError) as exc:
            errors.append(rid+': '+str(exc))
    # Cycles of CLOSED contracts cannot bootstrap one another.
    visiting, done = set(), set()
    def visit(rid):
        if rid in visiting:
            errors.append('cyclic CLOSED composition at '+rid); return
        if rid in done or rows[rid]['status']!='CLOSED': return
        visiting.add(rid)
        for child in rows[rid]['callees']:
            if child in rows: visit(child)
        visiting.remove(rid); done.add(rid)
    for rid in rows: visit(rid)
    return errors

def totals(data):
    result = {}
    for path in ['slice','thread']:
        subset = [r for r in data['rows'] if r['path']==path]
        count = Counter(r['status'] for r in subset)
        result[path] = dict(total=len(subset), BODY=sum(r['kind']=='BODY' for r in subset), LEAF=sum(r['kind']=='LEAF' for r in subset), **{k:count[k] for k in ['CLOSED','PARTIAL','OPEN']})
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger',type=Path,default=DEFAULT)
    parser.add_argument('--check',action='store_true',help='exit nonzero on any violation')
    parser.add_argument('--json',action='store_true')
    args = parser.parse_args()
    try:
        data = json.loads(args.ledger.read_text())
        errors = validate(data)
        counts = totals(data)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors, counts = [str(exc)], {}
    if args.json:
        print(json.dumps(dict(totals=counts,errors=errors),indent=2))
    else:
        for path,count in counts.items():
            print(path+': '+', '.join(f'{k}={v}' for k,v in count.items()))
        for error in errors:
            print('ERROR: '+error,file=sys.stderr)
        print('PASS' if not errors else f'FAIL ({len(errors)} violations)')
    return 1 if errors and args.check else 0

if __name__=='__main__':
    sys.exit(main())
