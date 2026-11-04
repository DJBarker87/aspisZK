"""Mutations cannot turn incomplete Box windows into a complete packet."""
import unittest,copy
from unittest.mock import patch
import NEX_check_box_windows as b
class Windows(unittest.TestCase):
 def test_common_positive_and_controls(self):self.assertEqual(b.common()['fields'],15)
 def test_missing_window(self):
  original=b.v.read
  def read(p):
   if str(p).endswith('NEX_K034-shape.json'):raise FileNotFoundError(p)
   return original(p)
  with patch.object(b.v,'read',side_effect=read),self.assertRaises(FileNotFoundError):b.common()
 def test_wrong_field_even_with_existing_pass(self):
  original=b.v.read
  def read(p):
   m=original(p)
   if str(p).endswith('NEX_K012-shape.json'):
    m=copy.deepcopy(m);m['native']=m['native'].replace('output_lane: bytes[7]','output_lane: bytes[6]')
   return m
  with patch.object(b.v,'read',side_effect=read),self.assertRaises(AssertionError):b.common()
 def test_wrong_window_index(self):
  original=b.v.read
  def read(p):
   m=original(p)
   if str(p).endswith('NEX_K034-shape.json'):m=copy.deepcopy(m);m['selected']=13
   return m
  with patch.object(b.v,'read',side_effect=read),self.assertRaises(AssertionError):b.common()
 def test_allocation_control_is_required(self):
  original=b.v.native
  def native(a,positive):
   if a=='NEX_K005':raise AssertionError('missing allocation control')
   return original(a,positive)
  with patch.object(b.v,'native',side_effect=native),self.assertRaises(AssertionError):b.common()
if __name__=='__main__':unittest.main()
