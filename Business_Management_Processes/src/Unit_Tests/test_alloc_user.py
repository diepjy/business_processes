from unittest import TestCase
from src.parser import p_c

__author__ = 'joanna'


class Test_alloc_user(TestCase):

    def setUp(self):
        print "test_alloc_user"

    def test_multi_authorised(self):
        s = p_c.p_c().main("Tasks: 't3', 't4'; Users: 'u3', 'u4'; Before: ('t3', 't4'); Authorised: ('t3', ['u3', 'u4']);")
        self.assertEqual(s, "sat")

    def test_authorised_senior_equality(self):
        s = p_c.p_c().main("Tasks: 't3' -min_sec_lv:!='t4', 't4'; Users: 'u3', 'u4'; Before: ('t3', 't4'); Authorised: ('t3', ['u3', 'u4']);")
        self.assertEqual(s, "sat")

