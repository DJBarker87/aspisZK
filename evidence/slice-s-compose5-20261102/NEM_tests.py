"""Mutation tests for additional certificate gates; inherited suites are separate."""
import unittest,copy,json,hashlib
import NEM_validate as v
class Fixtures(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEM_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEM_REVIEWED_CERTIFICATES.json')
 def check_mutation(self,mutate):
  c=copy.deepcopy(self.p['members'][v.DIGEST]);mutate(c)
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h
  r=copy.deepcopy(self.r);r[v.DIGEST]=h
  self.assertFalse(v.certificate(c,v.DIGEST,self.b,r))
class Certificates(Fixtures):
 def test_digest_accepted(self):self.assertTrue(v.certificate(self.p['members'][v.DIGEST],v.DIGEST,self.b,self.r))
 def test_missing(self):self.assertFalse(v.certificate(None,v.DIGEST,self.b,self.r))
 def test_wrong_count_invariant(self):self.check_mutation(lambda c:c['digest_composition'].update(invariant='count=0'))
 def test_no_native_pair(self):self.check_mutation(lambda c:c['digest_composition'].update(native_pairs=[]))
 def test_wrong_theorem(self):self.check_mutation(lambda c:c['digest_composition']['theorems'][0].update(name='NEM_DigestInstance.result_and_frame'))
 def test_wrong_source(self):self.check_mutation(lambda c:c['digest_composition'].update(frozen_body=''))
 def test_missing_frame(self):self.check_mutation(lambda c:c['call_domain_certificate'].update(native_frame_complete=False))
 def test_inner_domain(self):self.check_mutation(lambda c:c.update(inner_hypotheses_remaining=['Child.PacketDomain']))
 def test_wrong_arguments(self):self.check_mutation(lambda c:c['call_domain_certificate'].update(same_arguments=False))
 def test_extra_trust(self):self.check_mutation(lambda c:c['call_domain_certificate'].update(new_trust_rows=['NewTrust']))
class Common(Fixtures):
 def common_mutation(self,field,value):
  f='crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common';c=copy.deepcopy(self.p['members'][f]);c['common_composition'][field]=value
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[f]=h
  self.assertFalse(v.certificate(c,f,self.b,r))
 def test_no_common_windows(self):self.common_mutation('inherited_windows',[])
 def test_wrong_order(self):self.common_mutation('ordered_children',['common.nullifier','common.anchor_root','common.asset_id'])
 def test_wrong_frame(self):self.common_mutation('frame','all bytes may change')
 def test_wrong_width(self):self.common_mutation('reply_widths',[32,32,32])
 def test_missing_same_call(self):self.common_mutation('native_pairs',[])
class Payment(Fixtures):
 def mutate_payment(self,field,value):
  f='crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1';c=copy.deepcopy(self.p['members'][f]);c['payment_encode_composition'][field]=value
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[f]=h
  self.assertFalse(v.certificate(c,f,self.b,r))
 def test_missing_prefix(self):self.mutate_payment('prefix',[])
 def test_wrong_payment_field(self):self.mutate_payment('fields',['change_commitment','recipient_commitment'])
 def test_wrong_payment_window(self):self.mutate_payment('windows',[[148,32],[184,32]])
 def test_missing_payment_frame(self):self.mutate_payment('frames',[])
 def test_inner_payment_hypothesis(self):self.mutate_payment('no_inner_native_hypotheses',False)
class Lane(Fixtures):
 def mutate_lane(self,field,value):
  f='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1';c=copy.deepcopy(self.p['members'][f]);c['lane_composition'][field]=value
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[f]=h
  self.assertFalse(v.certificate(c,f,self.b,r))
 def test_wrong_nullifier(self):self.mutate_lane('child_log','canonical(other); first(other)')
 def test_missing_corrupt_control(self):self.mutate_lane('native_pairs',[['NEL_K002','NEL_K003']])
 def test_canonical_restriction(self):self.mutate_lane('all_raw_digests',False)
class FrontierValidator(Fixtures):
 def mutate_validator(self,field,value):
  f='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1';c=copy.deepcopy(self.p['members'][f]);c['frontier_validator'][field]=value
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[f]=h
  self.assertFalse(v.certificate(c,f,self.b,r))
 def test_missing_induction(self):self.mutate_validator('induction','')
 def test_missing_loop_step(self):self.mutate_validator('step',[])
 def test_wrong_validator_order(self):self.mutate_validator('ordered_children','frontier before root')
 def test_stronger_validator_domain(self):self.mutate_validator('all_raw_frontiers',False)
class Encoder(Fixtures):
 def mutate_encoder(self,field,value):
  f='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1';c=copy.deepcopy(self.p['members'][f]);c['encoder_composition'][field]=value
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[f]=h
  self.assertFalse(v.certificate(c,f,self.b,r))
 def test_missing_encoder_window(self):self.mutate_encoder('windows',[])
 def test_missing_native_encoder_step(self):self.mutate_encoder('native_pairs',[])
 def test_wrong_encoder_count(self):self.mutate_encoder('frontier',dict(base=160,count=19,width=32,destination_length=800))
 def test_missing_encoder_result(self):self.mutate_encoder('full_Result_state_effects',False)
 def test_missing_encoder_fill(self):self.mutate_encoder('std_fill_pin',{})
if __name__=='__main__':unittest.main()
