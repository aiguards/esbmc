import unittest

class Exprs(unittest.TestCase):
    # list of things to test: minmal creation, empty stuff,
    # typeid, pretty, equality + comparisons, clone, nested foo
    # downcasting, internal refs, all the kinds, non conversion,
    # cmps, the right exceptions thrown from failures, vectors
    # and the likes, composite kinds and their conents

    def make_unsigned(self, width=32):
        import esbmc
        return esbmc.type.unsignedbv.make(width)

    def make_bigint(self, value=0):
        import esbmc
        return esbmc.BigInt(value)

    def make_int(self, width=32, value=0):
        import esbmc
        u = self.make_unsigned(width)
        val = self.make_bigint(value)
        return esbmc.expr.constant_int.make(u, val)

    def test_min(self):
        import esbmc
        u32 = self.make_unsigned()
        zero = self.make_bigint()
        constint = esbmc.expr.constant_int.make(u32, zero)

        self.assertTrue(constint != None, "Can't create constant_int2t")

    def test_fields(self):
        import esbmc
        val = self.make_int()
        self.assertTrue(val.type == self.make_unsigned(), "Can't get expr type field")
        self.assertTrue(val.constant_value == self.make_bigint(), "Can't get expr value field")
        self.assertTrue(val.expr_id == esbmc.expr.expr_ids.constant_int, "Can't get expr value field")

    def test_cmps(self):
        import esbmc
        val0 = self.make_int(0)
        val1 = self.make_int(1)
        self.assertTrue(val0 == val0, "Same comparison should be true")
        self.assertFalse(val0 != val0, "Same comparison should still be true")
        self.assertTrue(val0 != val1, "Different comparision should be unequal")
        self.assertFalse(val0 == val1, "Different comparision shouldn't be equal")
        self.assertTrue(val0 < val1, "constints should compare less than")
        self.assertFalse(val1 < val0, "reversed constints should not compare less than")

    def test_pretty(self):
        import esbmc
        val = self.make_int()
        reftext = "constant_int\n* constant_value : 0\n* type : unsignedbv\n  * width : 32"
        self.assertTrue(val.pretty(0) == reftext, "Expr pretty should work")

    def test_clone(self):
        import esbmc
        val = self.make_int()
        val1 = val.clone()
        self.assertTrue(val == val1, "Cloned expr should be identical")
        self.assertFalse(val is val1, "Cloned expr should not be same object")

    def test_add(self):
        import esbmc
        val = self.make_int(1)
        val1 = self.make_int(2)
        add = esbmc.expr.add.make(val.type, val, val1)
        self.assertTrue(add.expr_id == esbmc.expr.expr_ids.add, "Add expr should have add id")
        self.assertTrue(add.side_1 == val, "Incorrect add2t field")
        self.assertTrue(add.side_2 == val1, "Incorrect add2t field")
        self.assertFalse(add.side_1 == val1, "add2t field shouldn't compare true")
        self.assertFalse(add.side_2 == val, "add2t field shouldn't compare true")
        # Accessing struct field should different python objects
        self.assertFalse(add.side_1 is val, "Incorrect python object comparison")
        self.assertFalse(add.side_2 is val1, "Incorrect python object comparison")
