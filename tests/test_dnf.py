from noodler import StringEquation, StringConstraint, ConstraintType

import unittest

class TestDNF(unittest.TestCase):

    def __init__(self, *args, **kwargs):
        super(TestDNF, self).__init__(*args, **kwargs)
        self.eq1 = StringEquation("xyz", "xyxy")
        self.eq2 = StringEquation("x", "y")
        self.eq3 = StringEquation("z", "w")

        self.ce1 = StringConstraint(ConstraintType.EQ, self.eq1)
        self.ce2 = StringConstraint(ConstraintType.EQ, self.eq2)
        self.ce3 = StringConstraint(ConstraintType.EQ, self.eq3)
        self.c1 = StringConstraint(ConstraintType.OR, self.ce1, self.ce2)
        self.c2 = StringConstraint(ConstraintType.AND, self.c1, self.ce3)

    def test_dnf1(self):
        print(self.c2)
        res = self.c2.to_dnf()
        print(res)
        assert res.op == ConstraintType.OR

    def test_dnf2(self):
        print(self.c1)
        res = self.c1.to_dnf()
        print(res)
        assert res.op == ConstraintType.OR


if __name__ == '__main__':
    unittest.main()
