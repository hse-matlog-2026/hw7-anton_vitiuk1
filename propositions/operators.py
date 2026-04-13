# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    from propositions.syntax import Formula

    return formula.substitute_operators({
        'T': Formula.parse('(p|~p)'),
        'F': Formula.parse('(p&~p)'),
        '->': Formula.parse('(~p|q)'),  # p -> q
        '+': Formula.parse('((p&~q)|(~p&q))'),  # xor
        '<->': Formula.parse('((p&q)|(~p&~q))'),  # iff
        '-&': Formula.parse('~(p&q)'),  # nand
        '-|': Formula.parse('~(p|q)')  # nor
    })

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    f = to_not_and_or(formula)
    return f.substitute_operators({
        '|': Formula.parse('~(~p&~q)')  # De Morgan
    })

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    f = to_not_and_or(formula)
    return f.substitute_operators({
        '~': Formula.parse('(p-&p)'),  # not p
        '&': Formula.parse('((p-&q)-&(p-&q))'),  # p&q
        '|': Formula.parse('((p-&p)-&(q-&q))')  # p|q
    })

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    f = to_not_and_or(formula)
    return f.substitute_operators({
        '&': Formula.parse('~(p->~q)'),  # p&q  ==  ~(p -> ~q)
        '|': Formula.parse('(~p->q)')  # p|q  ==  (~p -> q)
    })


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    f = to_not_and_or(formula)
    return f.substitute_operators({
        'T': Formula.parse('(F->F)'),  # True
        '~': Formula.parse('(p->F)'),  # not p
        '|': Formula.parse('((p->F)->q)'),  # p|q == (~p -> q)
        '&': Formula.parse('~(p->~q)')
    }).substitute_operators({
        # eliminate remaining '~' using (p->F)
        '~': Formula.parse('(p->F)')
    })
