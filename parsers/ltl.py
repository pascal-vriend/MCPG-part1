# !/usr/bin/python3
# -*- coding_ utf-8 -*-
import random

import ply.lex
import ply.yacc


class LTLLexer(object):
    keywords = {
        'true': 'TRUE',
        'false': 'FALSE',
        'X': 'NEXT',
        'U': 'UNTIL',
        'W': 'WEAKUNTIL',
        'F': 'EVENTUALLY',
        'G': 'GLOBALLY',
        'R': 'RELEASE',
        'M': 'STRONGRELEASE',
    }

    # List of token names.   This is always required
    tokens = (
                 'TERM',
                 'NOT',
                 'AND',
                 'OR',
                 'IMPLIES',
                 'EQUIV',
                 'LPAR',
                 'RPAR'
             ) + tuple(keywords.values())

    # Regular expression rules for simple tokens
    t_TRUE = r'true'
    t_FALSE = r'false'
    t_AND = r'\&'
    t_OR = r'\|'
    t_IMPLIES = r'\->'
    t_EQUIV = r'\<->'
    t_NOT = r'\~|!'
    t_LPAR = r'\('
    t_RPAR = r'\)'
    t_NEXT = r'X'
    t_UNTIL = r'U'
    t_WEAKUNTIL = r'W'
    t_RELEASE = r'R'
    t_STRONGRELEASE = r'M'
    t_EVENTUALLY = r'F'
    t_GLOBALLY = r'G'

    t_ignore = r' ' + '\n\t'

    def t_TERM(self, t):
        r'(?<![a-z])(?!true|false)[_a-z0-9]+'
        t.type = LTLLexer.keywords.get(t.value, 'TERM')
        return t

    def t_error(self, t):
        print("Illegal character '%s'" % t.value[0])
        t.lexer.skip(1)

    def __init__(self):
        self.lexer = ply.lex.lex(module=self)


class LTLParser(object):
    precedence = (
        ('nonassoc', 'LPAR', 'RPAR'),
        ('right', 'UNTIL', 'WEAKUNTIL', 'RELEASE', 'STRONGRELEASE'),
        ('left', 'AND', 'OR', 'IMPLIES', 'EQUIV'),
        ('right', 'EVENTUALLY', 'GLOBALLY'),
        ('right', 'NOT', 'NEXT'),
    )

    def __init__(self, dag):
        self.lexer = LTLLexer()
        self.tokens = self.lexer.tokens
        self.parser = ply.yacc.yacc(module=self)
        self.dag = dag

    def __call__(self, s, **kwargs):
        return self.parser.parse(s, lexer=self.lexer.lexer)

    def p_formula(self, p):
        """
        formula : formula AND formula
                | formula OR formula
                | formula IMPLIES formula
                | formula EQUIV formula
                | formula UNTIL formula
                | formula WEAKUNTIL formula
                | formula RELEASE formula
                | formula STRONGRELEASE formula
                | NEXT formula
                | EVENTUALLY formula
                | GLOBALLY formula
                | NOT formula
                | TRUE
                | FALSE
                | TERM
        """

        if len(p) == 2:
            p[0] = self.dag.make(p[1])
        elif len(p) == 3:
            if p[1] == '!':
                p[1] = '~'
            p[0] = self.dag.make(p[1], p[2])
        elif len(p) == 4:
            if p[2] == '->':
                p[0] = self.dag.make('|', ('~', p[1]), p[3])
            elif p[2] == '<->':
                p[0] = self.dag.make('|', ('&', p[1], p[3]), ('&', ('~', p[1]), ('~', p[3])))
            else:
                p[0] = self.dag.make(p[2], p[1], p[3])
        else:
            raise ValueError

    def p_expr_group(self, p):
        """
        formula : LPAR formula RPAR
        """
        p[0] = p[2]

    def p_error(self, p):
        raise ValueError("Syntax error in input! %s" % str(p))


class LTLPrefixParser(object):
    lexer: LTLLexer

    def __init__(self, dag):
        self.lexer = LTLLexer().lexer
        self.dag = dag

    def __call__(self, s, **kwargs):
        self.lexer.input(s)
        return self.parse_rec()

    def parse_rec(self):
        tok = self.lexer.token()
        if tok.type == 'TERM':
            return self.dag.make(tok.value)
        elif tok.type == 'TRUE':
            return 1
        elif tok.type == 'FALSE':
            return 0
        elif tok.type == 'NEXT':
            p = self.parse_rec()
            return self.dag.make('X', p)
        elif tok.type == 'EVENTUALLY':
            p = self.parse_rec()
            return self.dag.make('F', p)
        elif tok.type == 'GLOBALLY':
            p = self.parse_rec()
            return self.dag.make('G', p)
        elif tok.type == 'NOT':
            p = self.parse_rec()
            return self.dag.make('~', p)
        elif tok.type == 'AND':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('&', a, b)
        elif tok.type == 'OR':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('|', a, b)
        elif tok.type == 'IMPLIES':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('|', ('~', a), b)
        elif tok.type == 'EQUIV':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('|', ('&', a, b), ('&', ('~', a), ('~', b)))
        elif tok.type == 'UNTIL':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('U', a, b)
        elif tok.type == 'WEAKUNTIL':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('W', a, b)
        elif tok.type == 'RELEASE':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('R', a, b)
        elif tok.type == 'STRONGRELEASE':
            a = self.parse_rec()
            b = self.parse_rec()
            return self.dag.make('M', a, b)
        else:
            raise ValueError("Syntax error in input! %s" % str(tok))


def random_LTL(*props):
    three = ['U', 'W', 'M', 'R', '&', '|', '<->', '->']
    two = ['X', '!', 'F', 'G']
    one = ['true', 'false'] + list(props)
    while len(one) > 2*len(three):
        one += list(props)
    pool = one + two + three

    parts = []
    remaining = 1
    min_length = 4
    max_length = 20
    while remaining > 0:
        if len(parts) < min_length:
            tok = random.choice(two+three)
            if tok in three:
                remaining += 1
        elif len(parts) < max_length:
            tok = random.choice(pool)
            if tok in three:
                remaining += 1
            elif tok in ['true', 'false'] or tok in props:
                remaining -= 1
        else:
            tok = random.choice(props)
            remaining -= 1
        parts.append(tok)

    return ' '.join(parts)
