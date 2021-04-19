from noodler import AutSingleSEQuery, RESingleSEQuery, StringEquation


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

    re_bal = RESingleSEQuery(balanced, constraints)
    re_unbal = RESingleSEQuery(unbalanced, constraints)

    aut_bal = re_bal.aut_query()
    aut_unbal = re_unbal.aut_query()

    assert aut_bal.is_balanced()
    assert not aut_unbal.is_balanced()
