from unittest import TestCase
from src.parser import code_gen
from src.parser import p_c

__author__ = 'joanna'


class TestCode_gen(TestCase):

    def setUp(self):
        print "regular test"

    def test_get_smt_tasks_users(self):
        print "reg test"
        s = p_c.p_c().main("Tasks: 't1', 't2'; Users: 'u1', 'u2';")
        print s
        self.assertEqual(s, "sat")

    def test_smt_before(self):
        print "basic before test"
        s = p_c.p_c().main("Tasks: 't1', 't2'; Users: 'u1', 'u2'; Before: ('t1', 't2');")
        self.assertEqual(s, "sat")

    def test_smt_sod(self):
        print "basic sod test"
        s = p_c.p_c().main("Tasks: 't1', 't2'; Users: 'u1', 'u2'; SoD: ('t1','t2');")
        self.assertEqual(s, "sat")

    def test_smt_bod(self):
        print "basic bod test"
        s = p_c.p_c().main("Tasks: 't1', 't2'; Users: 'u1', 'u2'; BoD: ('t1','t2');")
        self.assertEqual(s, "sat")

    def test_seniority(self):
        print "basic bod test"
        s = p_c.p_c().main("Tasks: 't3', 't4'; Users: 'u3', 'u4'; Seniority: ('u3', 'u4');")
        self.assertEqual(s, "sat")

