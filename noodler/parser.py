"""
Parse smtlib (smt2) files with string constraints.

Relies on parser in Z3 and converts assertions into queries.

Classes:
--------
SmtlibParser
    Parses smt2 files and creates corresponding queries.
    The current implementation often fails due to Awali's
    limited support of rich alphabets. If Awali is changed
    for another library, this should work well (with corresponding
    adjustments).

SmtlibParserHackAbc
    Adjust SmtlibParser with translations of characters that
    are not compatible with Awali (see ``translate_for_awali``)
    into ASCI-control sequences.
"""

import itertools
from typing import Callable, Collection, Optional, Union

from .core import StringEquation, REConstraints, RE
from .sequery import MultiSEQuery

import awalipy
import z3


def awalipy_ratexp_plus(re: RE):
    """
    A wrapper that mimics the + operater in awalipy

    Parameters
    ----------
    re: RE

    Returns
    -------
    RE
        (re)+ = (re)(re)*
    """
    return awalipy.RatExp.mult(re, re.star())

# Symbol used to represent characters not included in alphabet of Awali REs
NONSPEC_SYMBOL = u"\x1A"


def translate_for_awali(string):
    # TODO \xff is in fact \xfffd in Z3.
    if string == "":
        return "\e"
    if "\xfffd" in string:
        string = string.replace("\xfffd", "\ufffd")
    string = bytes(string, 'ASCII').decode()
    tokens = {
        " ": "\x19",
        "<": "\x18",
        ">": "\x17",
        "?": "\x16",
        "\n": "\x15",
        ")": "\x14",
        "(": "\x13",
        "{": "\x12",
        "}": "\x11",
        "*": "\x10",
        ".": "\x09",
        "\\": "\x08",
        "\ufffd": "\x07",
    }
    return string #string.translate(str.maketrans(tokens))


def awalipy_allchar(alphabet: str) -> RE:
    """
    Create awalipy RE for Σ given as a string of characters.

    Parameters
    ----------
    alphabet: str

    Returns
    -------
    RE for a+b+c+...
    """
    all_str = '+'.join(alphabet)
    return awalipy.RatExp(all_str, alphabet=alphabet)


OPERATORS_Z3_TO_AWALIPY = {
    z3.Z3_OP_RE_PLUS : awalipy_ratexp_plus,
    z3.Z3_OP_RE_STAR : awalipy.RatExp.star,
    # Z3_OP_RE_OPTION : awalipy.RatExp.,
    z3.Z3_OP_RE_CONCAT : awalipy.RatExp.mult,
    z3.Z3_OP_RE_UNION : awalipy.RatExp.add,
    # Z3_OP_RE_RANGE : awalipy.RatExp.,
    # Z3_OP_RE_LOOP : awalipy.RatExp.,
    # Z3_OP_RE_INTERSECT : awalipy.RatExp.,
    # Z3_OP_RE_EMPTY_SET : awalipy.RatExp.,
    # Z3_OP_RE_FULL_SET : awalipy.RatExp.,
    # Z3_OP_RE_COMPLEMENT : awalipy.RatExp.,
}


def is_string_constant(ref: z3.SeqRef) -> bool:
    return ref.is_string_value()


def is_string_variable(ref: z3.SeqRef) -> bool:
    return ref.is_string() and ref.decl().kind() == z3.Z3_OP_UNINTERPRETED


def is_equation(ref):
    return ref.decl().kind() == z3.Z3_OP_EQ


def is_inre(ref):
    return ref.decl().kind() == z3.Z3_OP_SEQ_IN_RE


def is_assignment(ref: z3.BoolRef) -> bool:
    """
    Detect assignment.

    Assignment is an equation of the form `var = str_const`.

    Parameters
    ----------
    ref: z3 reference

    Returns
    -------
    True if `ref` is an assignment.
    """
    if ref.decl().kind() != z3.Z3_OP_EQ:
        return False

    left, right = ref.children()
    return is_string_variable(left) and is_string_constant(right)


class SmtlibParser:
    """
    Convert `.smt2` files into Queries.
    """

    def __init__(self, filename: str):
        self.filename: str = filename
        self.assertions: z3.z3.AstVector = z3.parse_smt2_file(filename)
        self.alphabet: Collection[str] = set()
        self.variables: Collection[str] = set()

        self.constraints: REConstraints = dict()
        self.equations: Collection[StringEquation] = []

        # Gather alphabet
        for ref in self.assertions:
            self._gather_symbols(ref)

        self.alphabet_str: str = "".join(self.alphabet) #+ NONSPEC_SYMBOL

        # Fresh variables
        self.next_variable_id = 0

    def fresh_variable(self) -> str:
        """
        Introduce and return (name of) a fresh variable.

        Creates a new variable, adds it into `variables`, and
        ensures that the same name will not be used by subsequent
        calls.

        Returns
        -------
        Name of a fresh variable.
        """
        prefix = 'noodler_var_'
        self.next_variable_id += 1
        new_var = f'{prefix}{self.next_variable_id-1}'
        self.variables.add(new_var)
        return new_var

    def _gather_symbols(self,
                        ref: Union[z3.ReRef, z3.SeqRef, z3.BoolRef]):
        """
        Detect string variables and RE-alphabet used in a z3 reference.

        Parameters
        ----------
        ref : z3.ReRef or z3.SeqRef or BoolRef
            z3 reference to regular expression, string,
            equation, or RE-query
        """
        # Strings (can appear from equations)
        if ref.sort().kind() == z3.Z3_SEQ_SORT:
            if is_string_constant(ref):
                self._extract_letters(ref)
                return
            elif is_string_variable(ref):
                self.variables.add(ref.as_string())
                return

        # Regular expressions or equation or re-query
        for child in ref.children():
            self._gather_symbols(child)

    def _extract_letters(self, ref: z3.SeqRef) -> None:
        """
        Update alphabet with letters given by z3.SeqRef.

        Parameters
        ----------
        ref: z3.SeqRef
        """
        self.alphabet.update(set(ref.as_string()))

    def z3_re_to_awali(self, ref: z3.ReRef) -> RE:
        """
        Convert z3 regular expression(RE) to Awalipy RE.

        Parameters
        ----------
        ref : z3.ReRef
            reference to RE
        Returns
        -------
        RE
            Awalipy representation of ref
        """
        z3_operator = ref.decl().kind()
        alphabet = self.alphabet_str

        # Basic blocks (string constants)
        if z3_operator == z3.Z3_OP_SEQ_TO_RE:
            string = ref.children()[0].as_string()
            return self.create_awali_re(string)

        # Allchar
        if ref.decl().name() == 're.allchar':
            return awalipy_allchar(alphabet)

        # Otherwise recursively convert children and glue them
        # together using appropriate operator
        #
        # 1. dict z3.operator -> awalipy operator
        # 2. convert children
        # 3. apply awalipy operator and return

        # 1. get awalipy operator
        if z3_operator not in OPERATORS_Z3_TO_AWALIPY:
            name = ref.decl().name()
            raise NotImplementedError(f"Z3 operator {z3_operator} ({name}) is "
                                      f"not implemented yet!")
        awalipy_op: Callable = OPERATORS_Z3_TO_AWALIPY[z3_operator]

        # 2. convert children
        child_re = [self.z3_re_to_awali(child) for child in ref.children()]

        # 3. apply awalipy operator
        return awalipy_op(*child_re)

    def create_awali_re(self, string):
        """
        Create Awalipy RatExp recognizing `string`.

        Parameters
        ----------
        string: str
            string term to be converted to Awali RE.

        Returns
        -------
        RE
            Awalipy representation of RE string.
        """
        return awalipy.RatExp(string, alphabet=self.alphabet_str)

    def parse_equation(self, ref: z3.BoolRef) -> StringEquation:
        left, right = ref.children()
        # TODO This restricts only to assignment-form of equations (like SSA-fragment)
        assert is_string_variable(left)
        assert right.sort_kind() == z3.Z3_SEQ_SORT

        res_left = [left.as_string()]

        def z3_concat_to_var_list(z3_ref: z3.SeqRef) -> Collection[str]:
            """
            Convert concatenation of string variables into list of vars.

            Parameters
            ----------
            z3_ref

            Returns
            -------
            List of variables from Z3_ref
            """
            if is_string_variable(z3_ref):
                return [z3_ref.as_string()]
            children = [z3_concat_to_var_list(child) for child in z3_ref.children()]
            return itertools.chain(*children)

        res_right = z3_concat_to_var_list(right)
        return StringEquation(res_left, list(res_right))

    def parse_re_constraint(self, ref: z3.BoolRef) -> REConstraints:
        """
        Translate one regular constraint into REConstraints dict.

        The reference should point to a Z3_OP_SEQ_IN_RE operator.

        Parameters
        ----------
        ref: z3.BoolRef to a in_re operator to translate

        Returns
        -------
        REConstraint
            Mapping `var -> RE`
        """
        assert is_inre(ref)
        left, right = ref.children()
        assert is_string_variable(left) and left.as_string() in self.variables

        return {left.as_string(): self.z3_re_to_awali(right)}

    def process_assignment(self, ref: z3.BoolRef) -> None:
        """
        Create a RE constraint or a fresh equation for literal assignment.

        Assignment is `var = str_cons`.
        If there is no RE constraint for `var`, we create one of the form
        `var → RE(str_cons)`. Otherwise we introduce a fresh variable (`x`)
        and create a new equation `var = x`, and introduce a constraint
        `x → RE(str_cons)`.

        Parameters
        ----------
        ref: z3.BoolRef of the form `var = string_const`

        Returns
        -------
        None
        """
        assert is_assignment(ref)
        var, const = (c.as_string() for c in ref.children())
        const_re: RE = self.create_awali_re(const)

        if var not in self.constraints:
            self.constraints[var] = const_re
        else:
            # Introduce a fresh variable and a new equation
            new_var = self.fresh_variable()
            self.constraints[new_var] = const_re
            self.equations.append(StringEquation([var],[new_var]))

    def parse_query(self) -> MultiSEQuery:
        # TODO might be or of equations

        for ref in self.assertions:
            if is_inre(ref):
                res = self.parse_re_constraint(ref)
                #  Assert that the variable does not have a constraint yet.
                # TODO: Two constraints for one variable would represent intersection of the two.
                assert res.keys().isdisjoint(self.constraints)
                self.constraints.update(res)

        # We need first all in_re constraints before processing assignments
        # for cases where we have both RE-constraint for `x` and an assignment
        # for `x`. This can be used to check for example whether "abc" ∈ L(RE).
        for ref in self.assertions:
            if is_inre(ref):
                continue

            if is_equation(ref) and not is_assignment(ref):
                equation = self.parse_equation(ref)
                self.equations.append(equation)

            elif is_assignment(ref):
                # Assignments are only stored for later processing
                self.process_assignment(ref)

            # The rest should be `or`
            else:
                # assert ref.decl().kind() == z3.Z3_OP_OR
                z3_operator, name = ref.decl().kind(), ref.decl().name()
                raise NotImplementedError(f"Z3 operator {z3_operator} ({name}) is "
                                          f"not implemented yet!")

        sigma_star: RE = awalipy_allchar(self.alphabet_str).star()
        for var in self.variables:
            self.constraints.setdefault(var, sigma_star)

        return MultiSEQuery(self.equations, self.constraints)


class SmtlibParserHackAbc(SmtlibParser):
    """
    Extend `SmtlibParser` with encoding of `<`,`>`, ` `, and
    other problematic characters using fresh ASCI symbols.

    This is ensured mainly by calls to ``translate_for_awali``
    """

    def __init__(self, filename: str):
        super(SmtlibParserHackAbc, self).__init__(filename)
        self.alphabet_str = translate_for_awali(self.alphabet_str)

    def create_awali_re(self, string):
        string = translate_for_awali(string)
        return super().create_awali_re(string)

    def _extract_letters(self, ref: z3.SeqRef) -> None:
        orig_string = ref.as_string()
        fixed_string = translate_for_awali(orig_string)
        self.alphabet.update(set(fixed_string))
