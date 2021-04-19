from noodler import StringEquation
from noodler.sequery import AutSingleSEQuery, RESingleSEQuery

e = StringEquation("xyz", "xyxy")
alph = "abc"
Sigma_exp = f"({'+'.join(alph)})"
Sigma_plus = f"{Sigma_exp}{Sigma_exp}*"
constraints = {
    "x" : Sigma_plus,
    "y" : f"{Sigma_exp}{Sigma_plus}",
    "z" : Sigma_plus
}
re_query = RESingleSEQuery(e, constraints)
query: AutSingleSEQuery = re_query.aut_query()
