from noodler import AutSingleSESystem, RESESystemSingle, StringEquation


def test_balanced():
    balanced = e = StringEquation("xyz", "xyx")
    unbalanced = StringEquation("xyz", "xyxy")

    alph = "abc"
    Sigma_exp = f"({'+'.join(alph)})"
    Sigma_plus = f"{Sigma_exp}{Sigma_exp}*"
    constraints = {
        "x": Sigma_plus,
        "y": f"{Sigma_exp}{Sigma_plus}",
        "z": Sigma_plus
    }

    re_bal = RESESystemSingle(balanced, constraints)
    re_unbal = RESESystemSingle(unbalanced, constraints)

    aut_bal = re_bal.aut_system()
    aut_unbal = re_unbal.aut_system()

    assert aut_bal.is_balanced()
    assert not aut_unbal.is_balanced()
