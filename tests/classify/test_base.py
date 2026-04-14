"""Tests for cstz.classify.base — Classified, ShapeWitness, Classifier."""

import pytest
from cstz.classify.base import Classified, ShapeWitness, Classifier
from cstz.classify.registry import DiscriminatorRegistry


class TestShapeWitness:
    def test_leaf(self):
        s = ShapeWitness(arity=0, roles=())
        assert s.arity == 0
        assert s.roles == ()

    def test_unary(self):
        s = ShapeWitness(arity=1, roles=("child",))
        assert s.arity == 1
        assert s.roles == ("child",)

    def test_binary(self):
        s = ShapeWitness(arity=2, roles=("left", "right"))
        assert s.arity == 2
        assert s.roles == ("left", "right")

    def test_arity_3_rejected(self):
        with pytest.raises(ValueError, match="binarized"):
            ShapeWitness(arity=3, roles=("a", "b", "c"))

    def test_arity_negative_rejected(self):
        with pytest.raises(ValueError, match="binarized"):
            ShapeWitness(arity=-1, roles=())

    def test_role_count_mismatch_rejected(self):
        with pytest.raises(ValueError, match="requires"):
            ShapeWitness(arity=2, roles=("only-one",))

    def test_leaf_with_roles_rejected(self):
        with pytest.raises(ValueError, match="requires"):
            ShapeWitness(arity=0, roles=("something",))

    def test_equality(self):
        assert ShapeWitness(0, ()) == ShapeWitness(0, ())
        assert ShapeWitness(2, ("l", "r")) == ShapeWitness(2, ("l", "r"))

    def test_frozen(self):
        s = ShapeWitness(0, ())
        with pytest.raises((AttributeError, TypeError)):
            s.arity = 1  # type: ignore


class TestClassified:
    def test_fields(self):
        c = Classified(tau=0b101, shape=ShapeWitness(0, ()))
        assert c.tau == 0b101
        assert c.shape.arity == 0

    def test_equality(self):
        a = Classified(tau=7, shape=ShapeWitness(0, ()))
        b = Classified(tau=7, shape=ShapeWitness(0, ()))
        assert a == b

    def test_frozen(self):
        c = Classified(tau=0, shape=ShapeWitness(0, ()))
        with pytest.raises((AttributeError, TypeError)):
            c.tau = 1  # type: ignore


class _LeafShapeClassifier(Classifier):
    """Minimal classifier: everything is a leaf."""
    def shape_of(self, node):
        return ShapeWitness(arity=0, roles=())


class TestClassifier:
    def _make_reg(self):
        reg = DiscriminatorRegistry()
        reg.register("is_int", lambda n: isinstance(n, int))
        reg.register("is_positive", lambda n: isinstance(n, int) and n > 0)
        reg.register("is_even", lambda n: isinstance(n, int) and n % 2 == 0)
        return reg

    def test_classify_empty_ids(self):
        """With no discriminator_ids, τ is always 0."""
        reg = self._make_reg()
        c = _LeafShapeClassifier(reg, ())
        assert c.classify(5).tau == 0
        assert c.classify(-3).tau == 0

    def test_classify_all_ids(self):
        """All fired discriminators OR into τ."""
        reg = self._make_reg()
        ids = tuple(d.id for d in reg.all())
        c = _LeafShapeClassifier(reg, ids)
        # 4 is int, positive, even → all three fire
        result = c.classify(4)
        assert result.tau == 0b111
        # -3 is int, not positive, not even → only is_int fires
        result = c.classify(-3)
        assert result.tau == 0b001

    def test_classify_subset(self):
        """Only listed discriminators are evaluated."""
        reg = self._make_reg()
        is_int = reg.get_by_name("is_int").id
        is_even = reg.get_by_name("is_even").id
        c = _LeafShapeClassifier(reg, (is_int, is_even))
        # 4: both fire; is_positive not evaluated
        result = c.classify(4)
        assert result.tau == (is_int | is_even)

    def test_missing_id_rejected(self):
        """discriminator_ids must all exist in the registry."""
        reg = self._make_reg()
        with pytest.raises(ValueError, match="not in registry"):
            _LeafShapeClassifier(reg, (999,))

    def test_shape_of_not_implemented(self):
        """Base Classifier.shape_of must be overridden."""
        reg = self._make_reg()
        c = Classifier(reg, ())
        with pytest.raises(NotImplementedError):
            c.classify(5)

    def test_idempotent(self):
        """M5 pre-verification: classify(n) twice returns identical."""
        reg = self._make_reg()
        ids = tuple(d.id for d in reg.all())
        c = _LeafShapeClassifier(reg, ids)
        a = c.classify(4)
        b = c.classify(4)
        assert a == b
        for _ in range(100):
            assert c.classify(4) == a

    def test_shape_passed_through(self):
        """shape_of() output is preserved in Classified."""
        reg = self._make_reg()

        class BinaryShape(Classifier):
            def shape_of(self, node):
                return ShapeWitness(2, ("l", "r"))

        c = BinaryShape(reg, ())
        result = c.classify("anything")
        assert result.shape.arity == 2
        assert result.shape.roles == ("l", "r")
