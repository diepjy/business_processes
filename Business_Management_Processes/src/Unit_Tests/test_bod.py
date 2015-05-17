from unittest import TestCase
from src.parser import p_c

__author__ = 'joanna'


class TestP_c(TestCase):

    def setUp(self):
        print "regular test"

    def test_bod_two(self):
        print "test_bod_two"
        s = p_c.p_c().main("Tasks: 't1', 't2', 't3'; Users: 'u1', 'u2', 'u3'; BoD: ('t1','t2'), ('t2', 't3');")
        self.assertEqual(s, "sat")

    def test_one_user_bod(self):
        print "test_one_user_sod"
        s = p_c.p_c().main("Tasks: 't1', 't2'; Users: 'u1'; BoD: ('t1','t2');")
        self.assertEqual(s, "sat")

    def test_bod_three(self):
        print "test_sod_three"
        s = p_c.p_c().main("Tasks: 't1', 't2', 't3'; Users: 'u1', 'u2', 'u3'; BoD: ('t1','t2'), ('t2', 't3'), ('t1', 't3');")
        self.assertEqual(s, "sat")

    def test_bod_sod_fail(self):
        print "test_bod_sod_fail"
        s = p_c.p_c().main("Tasks: 't0', 't1', 't2', 't3'; Users: 'u1'; BoD: ('t1', 't3'); SoD: ('t1', 't2');")
        self.assertEqual(s, "unsat")

    def test_bod_sod(self):
        print "test_bod_sod"
        s = p_c.p_c().main("Tasks: 't0', 't1', 't2', 't3'; Users: 'u1', 'u2'; BoD: ('t1', 't3'); SoD: ('t1', 't2');")
        self.assertEqual(s, "sat")