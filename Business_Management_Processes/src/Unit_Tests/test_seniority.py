from unittest import TestCase
from src.parser import p_c

__author__ = 'joanna'


class Test_seniority(TestCase):

    def setUp(self):
        print "test_seniority"

    def test_equal_seniority(self):
        s = p_c.p_c().main("Tasks: 't3' -min_sec_lv:='t4', 't4'; Users: 'u3', 'u4' -users:allocate; Seniority: ('u3', 'u4');")
        self.assertEqual(s, "sat")

    def test_equal_seniority_fail(self):
        s = p_c.p_c().main("Tasks: 't3' -min_sec_lv:='t4', 't4'; Users: 'u3', 'u4' -users:allocate; Seniority: ('u3', 'u4'); SoD: ('t3', 't4');")
        self.assertEqual(s, "unsat")

    def test_more_seniority(self):
        s = p_c.p_c().main("Tasks: 't3' -min_sec_lv:>'t4', 't4'; Users: 'u3', 'u4', 'u5', 'u6' -users:allocate; Seniority: ('u3', 'u4'), ('u5', 'u4'), ('u6', 'u5'); SoD: ('t3', 't4');")
        self.assertEqual(s, "sat")

    def test_less_seniority(self):
        s = p_c.p_c().main("Tasks: 't3' -min_sec_lv:<'t4', 't4'; Users: 'u3', 'u4', 'u5', 'u6' -users:allocate; Seniority: ('u3', 'u4'), ('u5', 'u4'), ('u6', 'u5'); SoD: ('t3', 't4');")
        self.assertEqual(s, "sat")

    def test_neq_seniority(self):
        s = p_c.p_c().main("Tasks: 't3' -min_sec_lv:!='t4', 't4'; Users: 'u3', 'u4', 'u5', 'u6' -users:allocate; Seniority: ('u3', 'u4'), ('u5', 'u4'), ('u6', 'u5'); SoD: ('t3', 't4');")
        self.assertEqual(s, "sat")