#!/usr/bin/env python3
"""Read/hash-only witness paths for the superseded B semantic-model context.

Run on the pinned host. This checks selected import witness paths, not a claim
that every transitive module has been enumerated or repaired.
"""
import argparse,hashlib,json,re
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def imports(text):
    # Remove nested Lean comments before reading import commands.
    out=[];i=depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text) if j<0 else j
        else:out.append(text[i]);i+=1
    return [m for line in ''.join(out).splitlines()
            if (match:=re.fullmatch(r'\s*(?:public |private )?import\s+([\w. ]+)\s*',line))
            for m in match[1].split()]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    work=Path('/home/dombarker/project-offloads/aspis-c2-owned-lean-20261017')
    env=work/'environment.json';e=json.loads(env.read_text())
    object_roots=[work/'objects',*[Path(s) for s in e['LEAN_PATH'].split(':')],Path('/tmp/aspis-mask432-enriched-refresh-20261016/objects')]
    frontier=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-typedfull-current-20261017/rejected-selected-read-cache-frontier.json')
    source_roots=[Path('/home/dombarker/project-offloads')/x/'sources' for x in [
        'aspis-r1-concrete-decoder-20261013','aspis-line18-import-footprint-20261013','aspis-fs-generic-20261006','aspis-r0-20261006','aspis-r1-mask-lean432-20261015']]
    source_roots+=[Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015/sources-final-bridge-recheck')]
    chains=[
      ['R1LiteralSemanticPrefix','R1SemanticPayloadView','R1SemanticRecordCodec','R1PrefixedStateCodec','R1TrailingStateFrame','FS2.DuplexDecode','FS2.Duplex','AspisV8R19.UniformStateFirstHit'],
      ['RawCutConstructedWords','RawCutCommitmentFrames','R1OpeningRecordCodec','R1LengthFrameCodec','R1PublicInitFrame','R1TrailingStateFrame','FS2.DuplexDecode','FS2.Duplex','AspisV8R19.UniformStateFirstHit'],
      ['R1LiteralSemanticPrefix','R1SemanticPayloadView','R1SemanticRecordCodec','R1SemanticCoefficientCodec','R1FoldedLeafCodec','R1WideExactLimbCodec','R0C.ModuloField','AspisFormal.CircleGroupOrder']]
    args.out.mkdir(parents=True,exist_ok=True)
    nodes={}
    for m in sorted(set(sum(chains,[]))):
        rel=Path(m.replace('.','/'))
        obj=next(p for r in object_roots if (p:=r/rel.with_suffix('.olean')).is_file())
        candidates=[r/rel.with_suffix('.lean') for r in source_roots]
        if m.startswith('RawCut'):
            candidates=[source_roots[-1]/rel.with_suffix('.lean'),*candidates]
        src=next(p for p in candidates if p.is_file())
        dest=args.out/'sources'/rel.with_suffix('.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
        nodes[m]={'source_path':str(src),'source_sha256':sha(src),'source_snapshot':str(dest.relative_to(args.out)),
                  'object_path':str(obj),'object_sha256':sha(obj),'direct_imports':imports(src.read_text())}
    for chain in chains:
        for a,b in zip(chain,chain[1:]):assert b in nodes[a]['direct_imports'],(a,b)
    comparison={}
    for m,f in json.loads(frontier.read_text()).items():
        h=nodes[m]['object_sha256'];comparison[m]={
            'resolved_object_sha256':h,'historical_object_sha256':f['historical_object_sha256'],
            'repaired_object_sha256':f['current_objects']['.olean']['sha256'],
            'matches_historical':h==f['historical_object_sha256'],
            'matches_repaired':h==f['current_objects']['.olean']['sha256']}
    assert comparison['FS2.Duplex']['matches_historical']
    assert comparison['AspisV8R19.UniformStateFirstHit']['matches_historical']
    assert comparison['AspisFormal.CircleGroupOrder']['matches_repaired']
    (args.out/'historical-environment.json').write_bytes(env.read_bytes())
    (args.out/'c-current-frontier.json').write_bytes(frontier.read_bytes())
    result={'classification':'HISTORICAL_CONTEXT_ONLY','affected_formal_results':13,
      'current_accepted_semantic_model_results':0,'scope':'Three explicit import witness paths; not an exhaustive closure audit or a rebuild.',
      'environment_sha256':sha(env),'frontier_sha256':sha(frontier),'object_search_roots':[str(r) for r in object_roots],
      'paths':chains,'nodes':nodes,'frontier':comparison,
      'reason':'Both B model targets reach old FS2.Duplex and UniformStateFirstHit objects. Circle resolves repaired05c7, not rejected39ea. Current primitive and fresh generic Core exclude these model imports.'}
    (args.out/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','classification':result['classification'],'results':13,'audit_sha256':sha(args.out/'audit.json')}))
if __name__=='__main__':main()
