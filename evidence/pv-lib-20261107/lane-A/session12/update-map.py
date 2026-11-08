"""Attach qualified prefix support, preserving every historical slot/status."""
from pathlib import Path
import json
E=Path(__file__).parent;root=E.parent.parent
support={
 'thread:f15 -> thread:f93':('PV_LIB_A_RangeTo270History12.history','Continuous3400-to270 entry on the corrected phase machine, under the existing165 semantics and its returned branch; every93 reply retained. Starts AFTER handles, not original entry. Native93 value binding and full backedge remain open.'),
 'thread:f15 -> thread:f166':('PV_LIB_A_RangeTo270History12.history','Same continuous history executes Some captures,3472 closure,3490 and166; None break, unknown tags and failed captures retain their source boundaries. No full166 Post or14756 claim.'),
 'thread:f166 -> thread:f269':('PV_LIB_A_F166Builder12.run','Exact7916 issue/full reply on corrected machine; all arms retained. Native constructor value/physical binding is not installed by this transport.'),
 'thread:f166 -> thread:f270':('PV_LIB_A_F166History12.run','Continuous166 prologue,269, captures and7934 to270 BODY entry; arbitrary stores/worlds/events/saved frames; failed and pending branches retained. Not270/361 completion.'),
 'thread:f15 :: storeAction93':('PV_LIB_A_RangeInvariant12.delivered','Arbitrary-iteration iterator facet through actual preparation/poll/delivery; saturated successor and no duplicate write on retries. Full loop backedge and prior-iteration framing remain OPEN; no deferred post-target cleanup was advanced.'),
 'thread:f6 :: machineTransport':('PV_LIB_A_F6History12.history','Continuous corrected f6 BODY-entry through FULL124 or first source/native stop. Not complete f6 Post, original-entry-to-f6, callback-to3400,361-through14756 or joint witness.'),
 'thread:f6 -> thread:f121':('PV_LIB_A_F6Constructors12.counter','Existing provider AtomicUsizeNew fact applied at exact1782 request yields held0 and world frame on return. The lower documented fact remains a parameter; no native runtime instance or complete constructor history binding is claimed.'),
 'thread:f6 -> thread:f123':('PV_LIB_A_F6Constructors12.panicked','Existing exact123 fact at1874 yields numeric held byte0 and world frame on return; existential representation kinds retained. The lower fact remains a parameter; not physical constructor adequacy.'),
 'thread:f6 -> thread:f124':('PV_LIB_A_F6Arc12.run','Actual1916 source operands/activation/destination/full reply transported. Native Arc value, source allocation/count and sparse physical image bindings remain open.')}
meta=dict(base='8abdcb48c52faeeb43f3f6144aed586a6a2569f4',target='D999 OwnInit prefix through14756; source7 closure',
 rule='LOG D999 / thread-5; inherited DEFERRED-POST-TARGET dispositions unchanged',
 prefix_support={k:dict(theorem=v[0],module=v[0].rsplit('.',1)[0],qualification=v[1]) for k,v in support.items()},
 table_surface='PV_LIB_A_StoreActionTable12: v2PrefixStep12/v2PrefixAdvance12/v2PrefixEntry12; SAME PARTIAL source machine; legacy v2 unchanged',
 row_closures=0,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,byte_images_defined=0,
 completion='PARTIAL: full requested completion not achieved; target not established')
p=root/'PLIB_MAP.json';m=json.loads(p.read_text());m['lane_A_session12']=meta
for slot in m['slots']:
 if slot['slot'] in meta['prefix_support']:slot['session12_prefix_support']=meta['prefix_support'][slot['slot']]
p.write_text(json.dumps(m,indent=2)+'\n')
(E/'MAP_DELTA.json').write_text(json.dumps(dict(scope=meta,slot_support=meta['prefix_support'],status_changes=0),indent=2)+'\n')
