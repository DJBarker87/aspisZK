#!/usr/bin/env python3
"""Derive an additive test from the existing fixture without changing production."""
from pathlib import Path
import hashlib,json,sys
root=Path(sys.argv[1]); p=root/'programs/aspis-pool/src/pair_forest_dispatch.rs'
s=p.read_text(); name='compact_dispatch_authenticates_selection_and_forwards_readonly_accounts'
start=s.index('    #[test]\n    fn '+name); end=s.index('\n    const _: ()',start)
test=s[start:end].replace(name,'r20_cpi_exact_bytes_and_order')
test=test.replace('        assert_eq!(invoked.data.len(), 320);', '        assert_eq!(invoked.data, encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap());\n        let expected = [proof.key, master.key, checkpoint.key, lane.key, registry.key, entry.key, verifier_checkpoint.key];\n        assert_eq!(invoked.accounts.iter().map(|a| a.pubkey).collect::<Vec<_>>(), expected.iter().map(|k| **k).collect::<Vec<_>>());\n        // A registry/entry permutation fails the real dispatch planner.\n        assert!(plan_pair_forest_terminal_dispatch_v1(&pool_program, &master, &checkpoint, &lane,\n            &policy, &[entry.clone(), registry.clone()], &verifier, &proof,\n            split_checkpoint, &request, 1).is_err());')
assert 'fn r20_cpi' not in s
cut=s.rfind('}'); p.write_text(s[:cut]+test+'\n'+s[cut:])
(root.parent/'dispatch-test-injection.json').write_text(json.dumps(dict(source=str(p.relative_to(root)),original_sha256=hashlib.sha256(s.encode()).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),derived_test_sha256=hashlib.sha256(test.encode()).hexdigest(),production_prefix_unchanged=True),indent=2)+'\n')
