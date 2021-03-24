from noodler import AutSESystem, RESESystem, StringEquation

e = StringEquation("xyz", "xyxy")
alph = "abc"
Sigma_exp = f"({'+'.join(alph)})"
Sigma_plus = f"{Sigma_exp}{Sigma_exp}*"
constraints = {
    "x" : Sigma_plus,
    "y" : f"{Sigma_exp}{Sigma_plus}",
    "z" : Sigma_plus
}
re_system = RESESystem(e, constraints)
system: AutSESystem = re_system.aut_system()
