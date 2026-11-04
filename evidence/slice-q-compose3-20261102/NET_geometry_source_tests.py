import unittest
import NET_geometry_source as s
class Source(unittest.TestCase):
 def test_positive(self):self.assertIn('PARTIAL',s.check()['status'])
 def deny(self,a,b):
  code=(s.E/'NET_geometry.rs.txt').read_text();self.assertIn(a,code)
  with self.assertRaises(AssertionError):s.check(code.replace(a,b))
 def test_gather_order(self):self.deny('flat.extend_from_slice(&values);\n lines.push(values[4]);','lines.push(values[4]);\n flat.extend_from_slice(&values);')
 def test_gather_value(self):self.deny('lines.push(values[4]);','lines.push(values[3]);')
 def test_zero(self):self.deny('*x==M31::ZERO','*x!=M31::ZERO')
 def test_backward_index(self):self.deny('suffix,prefixes[i],M31(reply[0])','suffix,prefixes[0],M31(reply[0])')
 def test_suffix_operand(self):self.deny('suffix,flat[i],M31(reply[1])','suffix,prefixes[i],M31(reply[1])')
if __name__=='__main__':unittest.main()
