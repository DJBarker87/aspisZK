import unittest
from aspis_completion.wire import *

class WireTests(unittest.TestCase):
    def test_every_frontier_length(self):
        for c in range(297):
            wire = Wire.parse(synthetic_body(c))
            self.assertEqual(len(wire.fields),697)
            self.assertEqual(len(wire.frontiers[0]),c)
            self.assertEqual(len(wire.frontiers[1]),c)
            self.assertEqual(len(wire.body),24890+52*c)
    def test_maximum(self):
        self.assertEqual(len(synthetic_body(296)),MAX_BODY_BYTES)
    def test_bad_lengths(self):
        for n in (0,11152,24889,24891,40283,40334):
            with self.assertRaises(WireError): Wire.parse(bytes(n))
    def test_fixed_noncanonical(self):
        for limb in (0,1,697*4-1):
            raw=bytearray(synthetic_body()); raw[limb*4:limb*4+4]=P.to_bytes(4,'little')
            with self.assertRaises(WireError): Wire.parse(raw)
    def test_same_body_mutation(self):
        old=Wire.parse(synthetic_body())
        raw=bytearray(old.body); raw[16]=1; new=Wire.parse(raw)
        self.assertEqual(old.roots,new.roots); self.assertEqual(old.records,new.records)
        self.assertNotEqual(old.fields,new.fields)
        self.assertNotEqual(old.digest,new.digest)
        with self.assertRaises(WireError): old.assert_same_body(new)
    def test_source_is_immutable(self):
        raw=bytearray(synthetic_body()); wire=Wire.parse(raw); raw[0]=1
        self.assertEqual(wire.fields[0][0],0)
    def test_packed_roundtrip(self):
        for n in (48,104):
            values=tuple((i*982451653) % P for i in range(n))
            self.assertEqual(unpack31(pack31(values),n),values)
    def test_packed_noncanonical(self):
        for offset,length in ((0,403),(403,186)):
            raw=bytearray(621); raw[offset:offset+length]=((P).to_bytes(length,'little'))
            with self.assertRaises(WireError): PackedRecord.parse(raw)
    def test_record_coordinates(self):
        c1=tuple(range(104));c2=tuple(range(48));salt=bytes(range(32))
        record=PackedRecord.parse(pack31(c1)+pack31(c2)+salt)
        self.assertEqual(record.c1(3,25),103)
        self.assertEqual(record.c2(2,3),(44,45,46,47))
        self.assertEqual(record.salt,salt)
    def test_parser_defers_record_check(self):
        raw=bytearray(synthetic_body());raw[11228:11232]=P.to_bytes(4,'little')
        Wire.parse(raw)
        with self.assertRaises(WireError): Wire.parse(raw,decode_records=True)
    def test_root_and_frontier_slices(self):
        raw=bytearray(synthetic_body(1));raw[11152:11178]=b'A'*26
        raw[11178:11204]=b'B'*26; raw[24890:24916]=b'C'*26;raw[24916:]=b'D'*26
        wire=Wire.parse(raw)
        self.assertEqual(wire.roots,(b'A'*26,b'B'*26))
        self.assertEqual(wire.frontiers,((b'C'*26,),(b'D'*26,)))

    def test_cannot_supply_stale_wire_fields(self):
        with self.assertRaises(TypeError):
            Wire(body=synthetic_body(), fields=((1,0,0,0),))
    def test_cannot_supply_stale_record_limbs(self):
        with self.assertRaises(WireError):
            PackedRecord(bytes(621), (1,)*104, (0,)*48, bytes(32))
