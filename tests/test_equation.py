from noodler import StringEquation

e = StringEquation("xyz", "xyxy")


def test_sides():
    assert e.vars == {"x", "y", "z"}
    assert e.get_side("left") == e.left
    assert e.get_side("right") == e.right


def test_switched():
    assert e.switched.vars == e.vars
    assert e.switched.switched == e
    assert e.left == e.switched.right
    assert e.right == e.switched.left
