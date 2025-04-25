# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from src.logic_utils import (
    frozen,
    memoized_parameterless_method,
)

from src.propositions.syntax import (
    Formula as PropositionalFormula,
)


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """

    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (
        ((string[0] >= "0" and string[0] <= "9") or (string[0] >= "a" and string[0] <= "e")) and string.isalnum()
    ) or string == "_"


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= "u" and string[0] <= "z" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= "f" and string[0] <= "t" and string.isalnum()

def separate_bracketed_formula(text: str) -> Tuple:
    if (op := text[0]) not in {'[', '('}:
        print(f"{text} doesn't start with a bracket")
        return text
    cl = ']' if op == '[' else ')'
    bal = 0
    for i, ch in enumerate(text):
        if ch == op:
            bal += 1
        if ch == cl:
            bal -= 1
        if bal == 0:
            return text[:i+1], text[i+1:]

def split_function_or_relation(text: str) -> Tuple:
    assert text
    idx = 0
    while text[idx].isalnum():
        idx += 1
    return text[:idx], *separate_bracketed_formula(text[idx:])

def split_term(text: str) -> Tuple:
    assert text
    ch = text[0]
    if ch == '_':
        return '_', text[1:]
    idx = 0
    while idx < len(text) and text[idx].isalnum():
        idx += 1
    if is_constant(ch) or is_variable(ch):
        return text[:idx], text[idx:]
    assert is_function(ch)
    args, tail = separate_bracketed_formula(text[idx:])
    return text[:idx] + args, tail


@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        current_root = self.root
        if is_variable(current_root) or is_constant(current_root):
            return current_root
        arguments = [arg.__repr__() for arg in self.arguments]
        return f'{current_root}({",".join(arguments)})'
        # Task 7.1

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        if string:
            first = string[0]
            if is_constant(first) or is_variable(first):
                name, rest = split_term(string)
                return Term(name), rest
            assert is_function(first)
            func, args, rem = split_function_or_relation(string)
            inside = args[1:-1]
            parts = []
            while inside:
                head, inside = split_term(inside)
                parts.append(head)
                if inside and inside[0] == ',':
                    inside = inside[1:]
            terms = [Term._parse_prefix(p)[0] for p in parts]
            return Term(func, terms), rem
        # Task 7.3a

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        t = Term._parse_prefix(string)[0]
        assert string == str(t := Term._parse_prefix(string)[0])
        return t

        # Task 7.3b

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5a
        r = self.root
        if is_constant(r): return {r}
        if is_variable(r): return set()
        s = set()
        for a in self.arguments: s |= Term.constants(a)
        return s

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5b
        r = self.root
        if is_variable(r): return {r}
        if is_constant(r): return set()
        s = set()
        for a in self.arguments: s |= Term.variables(a)
        return s

    def functions(self) -> Set[Tuple[str, int]]:
        r = self.root
        s = set()
        if is_function(r):
            s |= {(r, len(self.arguments))}
            for a in self.arguments: s |= a.functions()
        return s

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == "="


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= "F" and string[0] <= "T" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == "~"


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == "&" or string == "|" or string == "->"


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == "A" or string == "E"

def split_op(s: str) -> list:
    return (s[0], s[1:]) if s[0] in {'&','|','+'} else (s[:2], s[2:]) if s[:2] in {'->','-&','-|'} else (s[:3], s[3:])

@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    statement: Optional[Formula]

    def __init__(
        self,
        root: str,
        arguments_or_first_or_variable: Union[Sequence[Term], Formula, str],
        second_or_statement: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(arguments_or_first_or_variable, Sequence) and not isinstance(
                arguments_or_first_or_variable, str
            )
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = root, tuple(arguments_or_first_or_variable)
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is not None
            self.root, self.first, self.second = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(arguments_or_first_or_variable, str) and is_variable(arguments_or_first_or_variable)
            assert second_or_statement is not None
            self.root, self.variable, self.statement = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        current_root = self.root

        if is_equality(current_root):
            left = self.arguments[0].__repr__()
            right = self.arguments[1].__repr__()
            return f'{left}{current_root}{right}'

        if is_relation(current_root):
            args = [arg.__repr__() for arg in self.arguments]
            return f'{current_root}({",".join(args)})'

        if is_unary(current_root):
            subformula = self.first.__repr__()
            return f'{current_root}{subformula}'

        if is_binary(current_root):
            left = self.first.__repr__()
            right = self.second.__repr__()
            return f'({left}{current_root}{right})'

        # если не попало никуда выше, значит квантор
        assert is_quantifier(current_root)
        inner = self.statement.__repr__()
        return f'{current_root}{self.variable}[{inner}]'
        # Task 7.2

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        if not string:
            raise ValueError(string)

        c = string[0]

        if is_constant(c) or is_variable(c) or is_function(c):
            a, b = split_term(string)
            if not b or b[0] != '=':
                raise ValueError(string)
            d, e = split_term(b[1:])
            return Formula('=', [Term.parse(a), Term.parse(d)]), e

        if is_relation(c):
            r, s, t = split_function_or_relation(string)
            u = s[1:-1]
            v = []
            while u:
                w, u = split_term(u)
                v.append(Term.parse(w))
                if u and u[0] == ',':
                    u = u[1:]
            return Formula(r, v), t

        if is_unary(c):
            f, g = Formula._parse_prefix(string[1:])
            return Formula(c, f), g

        if c == '(':
            h, i = Formula._parse_prefix(string[1:])
            j, i = split_op(i)
            k, i = Formula._parse_prefix(i)
            if not i or i[0] != ')':
                raise ValueError(i)
            return Formula(j, h, k), i[1:]

        if is_quantifier(c):
            m = string.find('[')
            n = string[1:m]
            if not n:
                raise ValueError(string)
            p, q = separate_bracketed_formula(string[m:])
            r, s = Formula._parse_prefix(p[1:-1])
            if s:
                raise ValueError(s)
            return Formula(c, n, r), q

        raise ValueError(string)

    @staticmethod
    def parse(string: str) -> Formula:
        f = Formula._parse_prefix(string)[0];
        assert string == str(f);
        return f

        # Task 7.4b

    def _apply_on_args(self, f):
        s = set()
        for a in self.arguments: s |= f(a)
        return s

    def constants(self) -> Set[str]:
        r = self.root
        if is_quantifier(r): return self.statement.constants()
        if is_unary(r): return self.first.constants()
        if is_binary(r): return self.first.constants() | self.second.constants()
        return self._apply_on_args(lambda a: a.constants())

    def variables(self) -> Set[str]:
        r = self.root
        if is_quantifier(r): return self.statement.variables() | {self.variable}
        if is_unary(r): return self.first.variables()
        if is_binary(r): return self.first.variables() | self.second.variables()
        return self._apply_on_args(lambda a: a.variables())

    def free_variables(self) -> Set[str]:
        r = self.root
        if is_quantifier(r): return self.statement.free_variables() - {self.variable}
        if is_unary(r): return self.first.free_variables()
        if is_binary(r): return self.first.free_variables() | self.second.free_variables()
        return self._apply_on_args(lambda a: a.variables())

    def functions(self) -> Set[Tuple[str, int]]:
        r = self.root
        if is_quantifier(r): return self.statement.functions()
        if is_unary(r): return self.first.functions()
        if is_binary(r): return self.first.functions() | self.second.functions()
        return self._apply_on_args(lambda a: a.functions())

    def relations(self) -> Set[Tuple[str, int]]:
        r = self.root
        if is_relation(r): return {(r, len(self.arguments))}
        if is_quantifier(r): return self.statement.relations()
        if is_unary(r): return self.first.relations()
        if is_binary(r): return self.first.relations() | self.second.relations()
        return set()

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term
        `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

    def propositional_skeleton(
        self,
    ) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name, equality, or quantifier at its
            root with a propositional variable name, consistently such that
            multiple identical such (outermost) subformulas are substituted with
            the same propositional variable name. The propositional variable
            names used for substitution are obtained, from left to right
            (considering their first occurrence), by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula, substitution_map: Mapping[str, Formula]) -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
