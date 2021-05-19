from typing import Collection, Optional, Union

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
    return awalipy.RatExp.mult(re, awalipy.RatExp.star(re))


NONSPEC_SYMBOL = u"\x1A"


def translate_for_awali(string):
    # TODO \xff is in fact \xfffd in Z3.
    if string == "":
        return "\e"
    if "\xfffd" in string:
        string = string.replace("\xfffd", "\ufffd")
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
        "\ufffd": "\x08",
    }
    return string.translate(str.maketrans(tokens))


def awalipy_allchar(alphabet):
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

        # Gather alphabet
        for ref in self.assertions:
            self._gather_symbols(ref)

        self.alphabet_str: str = "".join(self.alphabet) + NONSPEC_SYMBOL

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

        # Otherwise recursively convert children and glue the
        # together using appropriate operator
        #
        # 1. define function with fixed alphabet
        # 2. dict z3.operator -> awalipy operator
        # 3. convert children
        # 4. apply awalipy operator and return

        # 1. define function with fixed alphabet for recursive calls
        # using map
        def fix_alpha_for_rec(child_ref):
            return self.z3_re_to_awali(child_ref)

        # 2. get awalipy operator
        if z3_operator not in OPERATORS_Z3_TO_AWALIPY:
            name = ref.decl().name()
            raise NotImplementedError(f"Z3 operator {z3_operator} ({name}) is "
                                      f"not implemented yet!")
        awalipy_op = OPERATORS_Z3_TO_AWALIPY[z3_operator]

        # 3. convert children
        child_re = map(fix_alpha_for_rec, ref.children())

        # 4. apply awalipy operator
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

    def process_equation(self, ref: z3.BoolRef) -> StringEquation:
        pass

    def process_re_constraint(self, ref: z3.BoolRef) -> REConstraints:
        """
        Translate one regular constraint into REConstraints dict.

        The reference should point to a Z3_OP_SEQ_IN_RE operator where
        the left side is a variable.

        Parameters
        ----------
        ref: z3.BoolRef to a in_re operator
            constraint to translate

        Returns
        -------
        REConstraint
            Mapping `var -> RE`
        """
        assert ref.decl().kind() == z3.Z3_OP_SEQ_IN_RE
        left, right = ref.children()
        assert is_string_variable(left)
        assert left.as_string() in self.variables

        return {left.as_string() : self.z3_re_to_awali(right)}

    def parse_query(self) -> MultiSEQuery:
        # TODO equations
        # TODO might be or of equations
        for ref in self.assertions:
            if is_inre(ref):
                res = self.process_re_constraint(ref)
                assert res.keys().isdisjoint(self.constraints)
                self.constraints.update(res)

class SmtlibParserHackAbc(SmtlibParser):
    """
    Extend `SmtlibParser` with encoding of `<`,`>`, ` `, and
    non-asci characters using fresh ASCI symbols.
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


def smt2_to_query(filename: str) -> MultiSEQuery:
    ast_vect: z3.z3.AstVector = z3.parse_smt2_file(filename)

    for ast in ast_vect:
        assert isinstance(ast, z3.BoolRef)
    pass
