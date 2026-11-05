from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1]);assert 11<=n<=21
s=(E/'NHB_ghost_contains.rs.txt').read_text().replace('11<=n && n<22',f'n=={n}').replace('a[..n].contains(&x)',f'a[..{n}].contains(&x)')
(E/'NHB_constant_contains.rs.txt').write_text(s)
(E/'NHB_CONSTANT_CONTAINS.json').write_text(json.dumps(dict(length=n,actual_slice_bound='literal, equal to required n',postcondition='scalar expected pre-observation; no array capture',domain='canonical22, inactive zero and x18, expected uniquely equals natural prefix predicate',mode='constant-length reduction of unresolved helper, unchanged name'),indent=2)+'\n')
