#!/usr/bin/env python3
"""Git-exact source/constructor inventory; no compiler or formal proof job."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
BASE = 'docs/research/100bit-spend-path-20261013'
sha = lambda b: hashlib.sha256(b).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--revision', required=True)
    ap.add_argument('--output', type=Path, default=ROOT / BASE / 'evidence/c2-word-origin-20261016/source-inventory.json')
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args(); ref = git('rev-parse', a.revision).decode().strip()
    def read(path): return git('show', ref + ':' + path)
    lexer_path = BASE + '/tools/j1e-source-effect-audit.py'
    assert (ROOT / lexer_path).read_bytes() == read(lexer_path)
    spec = importlib.util.spec_from_file_location('source_lexer', ROOT / lexer_path)
    audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
    tree = git('ls-tree', '-r', '-z', ref, '--', 'crates', 'programs').split(b'\0')
    files = []
    for item in tree:
        if not item: continue
        metadata, raw_path = item.split(b'\t', 1); path = raw_path.decode()
        if not path.endswith('.rs'): continue
        raw = read(path); text = raw.decode(); ts = audit.tokens(text)
        hits = {word: [text.count('\n', 0, t[1]) + 1 for t in ts if t[0] == word]
                for word in ['C2Word', 'literalMessage']}
        files.append({'path': path, 'git_blob': metadata.decode().split()[-1], 'sha256': sha(raw),
                      'bytes': len(raw), 'identifier_hits': hits,
                      'raw_substring_counts': {w: text.count(w) for w in hits}})
    assert files and not any(any(x['identifier_hits'].values()) for x in files)
    assert not any(any(x['raw_substring_counts'].values()) for x in files)
    declarations = []
    def rust(path, anchor, label):
        raw = read(path); body, start, end, first, last = audit.fragment(raw, anchor)
        declarations.append({'id': label, 'path': path, 'language': 'Rust', 'anchor': anchor,
            'source_file_sha256': sha(raw), 'declaration_sha256': sha(body.encode()),
            'start_byte': start, 'end_byte_exclusive': end, 'first_line': first, 'last_line': last,
            'boundary_method': 'Pinned lexical balanced-brace fragment; attributes/docs outside anchor line excluded',
            'source': body})
    def lean(file, name, label):
        path = BASE + '/lean/' + file + '.lean'; raw = read(path); text = raw.decode()
        pat = r'(?m)^(?:private )?(?:noncomputable )?(?:def|abbrev|inductive|structure|theorem) ' + re.escape(name) + r'(?=\s|\(|:|$)'
        matches = list(re.finditer(pat, text)); assert len(matches) == 1, (path, name)
        start = matches[0].start()
        stop = re.search(r'(?m)^(?:/--|(?:private )?(?:noncomputable )?(?:def|abbrev|inductive|structure|theorem) |#print axioms|end(?: |$))', text[matches[0].end():])
        end = matches[0].end() + stop.start() if stop else len(text)
        body = text[start:end].rstrip(); end = start + len(body)
        declarations.append({'id': label, 'path': path, 'language': 'Lean', 'declaration': name,
            'source_file_sha256': sha(raw), 'declaration_sha256': sha(body.encode()),
            'start_byte': len(text[:start].encode()), 'end_byte_exclusive': len(text[:end].encode()),
            'first_line': text.count('\n', 0, start)+1, 'last_line': text.count('\n', 0, end)+1,
            'boundary_method': 'Exact top-level source slice through next declaration/documentation/axioms/end boundary; not Lean elaboration',
            'source': body})
    R = 'crates/aspis-r1-cost-probe/src/'
    for path, anchor, label in [
        (R+'host_semantic.rs', '    fn build_with_helper_mode<', 'host-semantic-build'),
        (R+'host_semantic.rs', 'pub fn build_with_material<', 'host-semantic-material'),
        (R+'prover.rs', '    fn c2(&mut self,columns:', 'backend-c2'),
        (R+'prover.rs', 'pub struct Backend {', 'backend-owned-data'),
        (R+'prover.rs', 'pub fn prove_masked_attempt(', 'host-attempt-entry'),
        (R+'prover.rs', 'fn prove_masked_with_attempt(', 'host-attempt-material'),
        (R+'prover.rs', 'fn prove_from_semantics(', 'host-proof-serialization'),
        (R+'host_commitment.rs', '    fn build(', 'commitment-build'),
        (R+'host_commitment.rs', 'pub struct Commitment {', 'commitment-owned-data'),
        (R+'host_commitment.rs', '    pub fn encode<', 'domain-encode'),
        (R+'host_commitment.rs', '    pub(crate) fn fill_opening(', 'commitment-fill-opening'),
        (R+'transport.rs', '    pub fn coefficients<', 'variant-coefficients'),
        (R+'verifier.rs', "    pub fn parse(bytes:", 'verifier-parse'),
        (R+'verifier.rs', 'fn query_with_geometry<', 'verifier-query'),
        (R+'verifier.rs', 'pub fn tx1<', 'verifier-tx1'),
        (R+'verifier.rs', 'pub fn tx2_authenticated<', 'verifier-tx2-authenticated'),
        (R+'r1_wire.rs', "    pub fn parse(bytes:", 'prefix-parse'),
        ('programs/r1-cost-probe/src/lib.rs', 'fn first(', 'program-first'),
        ('programs/r1-cost-probe/src/r1_pool_adapter.rs', 'fn stage1(', 'adapter-stage1'),
        ('programs/r1-cost-probe/src/r1_pool_adapter.rs', 'fn stage2(', 'adapter-stage2'),
        ('programs/r1-cost-probe/src/r1_pool_adapter.rs', 'fn require_readonly_buffer(', 'readonly-buffer-wrapper'),
        ('crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs', 'pub fn build_pool_v1_pair_forest_copy_helper_v1(', 'helper-h1-origin'),
        ('crates/aspis-prover/src/state_only_hiding.rs', 'pub fn apply_pool_v1_pair_forest_h1_padding_mask_v1(', 'helper-h1-padding'),
        ('crates/aspis-core/src/state_only_private_merkle.rs', 'pub fn private_leaf_hash_with_digest<', 'private-c2-leaf-grammar'),
    ]: rust(path, anchor, label)
    for file, name, label in [
        ('LiteralTypedWords', 'C2Word', 'model-c2-word-type'),
        ('MixedLeafEncoding', 'C2Slot', 'model-c2-slot-type'),
        ('LiteralTranscript', 'Message', 'model-message-carrier'),
        ('LiteralTranscript', 'erase', 'model-erase'),
        ('CanonicalLiteralProof', 'zeroC2', 'canonical-zero-c2'),
        ('CanonicalLiteralProof', 'literalMessage', 'canonical-literal-message'),
        ('CanonicalCutEnrichedTranscript', 'wordsFromMaps', 'cut-words-from-maps'),
        ('CanonicalCutEnrichedTranscript', 'rawC2Map', 'cut-c2-packed-map'),
        ('CanonicalCutEnrichedTranscript', 'enrichMessage', 'cut-enrich-message'),
        ('TypedRecoveredWords', 'c2Value', 'cut-c2-value'),
        ('LiteralSemanticPrefix', 'c2Pair', 'model-semantic-c2-pair'),
        ('LiteralSemanticPrefix', 'parseMessage', 'model-semantic-parser'),
        ('LiteralSemanticPayloadBridge', 'read_of_decodeFull_atC2', 'model-c2-read-obligation'),
        ('RawCutProverCompiler', 'compiled', 'recorded-experiment-compiler'),
        ('RawCutWordsFromView', 'buildWords', 'recorded-view-words'),
        ('RawCutConstructedWords', 'buildWords_eq_full_from_messages', 'recorded-view-parser-premises'),
        ('RawByteCutStability', 'recoverAt', 'recorded-cut-recovery'),
        ('RawByteCutStability', 'all_paths_stable', 'recorded-cut-stability-premises'),
    ]: lean(file, name, label)
    result = {'source_revision': ref, 'script_sha256': sha(Path(__file__).read_bytes()),
        'negative_inventory': {'scope': 'Every tracked .rs blob under crates/ and programs/ at this exact Git revision, including tests/examples/cfg alternatives; no untracked/generated/vendor/expanded macro output or archive claim',
            'files_scanned': len(files), 'files': files, 'exact_identifiers': ['C2Word','literalMessage'],
            'identifier_hits': 0, 'raw_substring_hits': 0,
            'conclusion': 'No explicit C2Word or literalMessage source identifier occurs in this production-source inventory. This is an inventory negative, not a Rust elaboration theorem or a claim that macros/foreign binaries were inspected.'},
        'declarations': declarations,
        'formal_status': 'Source design/inventory only. No Lean/Rust/Aeneas/SBF/runtime execution, no new theorem or axiom, no #print axioms result claimed.'}
    encoded = (json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
    if a.check: assert a.output.read_bytes() == encoded
    else: a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(encoded)
    print(json.dumps({'revision':ref,'files_scanned':len(files),'declarations':len(declarations),'negative_identifier_hits':0,'output_sha256':sha(encoded)},sort_keys=True))
if __name__ == '__main__': main()
