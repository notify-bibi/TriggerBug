import base64
import hashlib
import json
import sqlite3
import sys
import xml.dom.minidom as xmldom
from lxml import etree
import time
from re import findall
import requests
import pickle
import re

html=None
with open("./Intel® Intrinsics Guide.html")as f:
    html=f.read()



class Stack(object):
    """
    The structure of a Stack.
    The user don't have to know the definition.
    """
    def __init__(self):
        self.__container = list()
    def __is_empty(self):
        """
        Test if the stack is empty or not
        :return: True or False
        """
        return len(self.__container) == 0

    def num(self):
        return len(self.__container)

    def push(self, element):
        """
        Add a new element to the stack
        :param element: the element you want to add
        :return: None
        """
        self.__container.append(element)
    def top(self):
        """
        Get the top element of the stack
        :return: top element
        """
        if self.__is_empty():
            return None
        return self.__container[-1]
    def pop(self):
        """
        Remove the top element of the stack
        :return: None or the top element of the stack
        """
        return None if self.__is_empty() else self.__container.pop()
    def clear(self):
        """
        We'll make an empty stack
        :return: self
        """
        self.__container.clear()
        return self

    def get(self):
        return self.__container[:]

    def __str__(self):
        if self.__is_empty():
            return "None"
        t = "["
        for i in self.__container:
            t += " \""+i.__str__() + "\", "
        return  t[:-2]+"]"


class Calculator(object):
    """
    A simple calculator, just for fun
    """
    def __init__(self):
        self.__exp = ''
    def __validate(self):
        """
        We have to make sure the expression is legal.
        1. We only accept the `()` to specify the priority of a sub-expression. Notes: `[ {` and `] }` will be
        replaced by `(` and `)` respectively.
        2. Valid characters should be `+`, `-`, `*`, `/`, `(`, `)` and numbers(int, float)
        - Invalid expression examples, but we can only handle the 4th case. The implementation will
        be much more sophisticated if we want to handle all the possible cases.:
            1. `a+b-+c`
            2. `a+b+-`
            3. `a+(b+c`
            4. `a+(+b-)`
            5. etc
        :return: True or False
        """
        if not isinstance(self.__exp, str):
            print('Error: {}: expression should be a string'.format(self.__exp))
            return False
        # Save the non-space expression
        val_exp = ''
        s = Stack()
        for x in self.__exp:
            # We should ignore the space characters
            if x == ' ':
                continue
            if self.__is_bracket(x) or self.__is_digit(x) or self.__is_operators(x) \
                    or x == '.':
                if x == '(':
                    s.push(x)
                elif x == ')':
                    s.pop()
                val_exp += x
            else:
                print('Error: {}: invalid character: {}'.format(self.__exp, x))
                return False
        if s.top():
            print('Error: {}: missing ")", please check your expression'.format(self.__exp))
            return False
        self.__exp = val_exp
        return True
    def __convert2postfix_exp(self, expr):
        """
        Convert the infix expression to a postfix expression
        :return: the converted expression
        """
        # highest priority: ()
        # middle: * /
        # lowest: + -
        converted_exp = ''
        stk = Stack()
        method = ''
        for i,x in enumerate(expr) :
            if self.__is_method(method + expr[i:]):
                method += x
                if self.__is_method(method):
                    stk.push(method)
                    method=""
                continue

            if self.__is_digit(x) or x == '.':
                converted_exp += x
            elif self.__is_operators(x):
                converted_exp += ' '
                tp = stk.top()
                if tp:
                    if tp == '(':
                        stk.push(x)
                        continue
                    x_pri = self.__get_priority(x)
                    tp_pri = self.__get_priority(tp)
                    if x_pri > tp_pri:
                        stk.push(x)
                    elif x_pri == tp_pri:
                        converted_exp += stk.pop() + ' '
                        stk.push(x)
                    else:
                        while stk.top():
                            if self.__get_priority(stk.top()) != x_pri:
                                converted_exp += stk.pop() + ' '
                            else:
                                break
                        stk.push(x)
                else:
                    stk.push(x)
            elif self.__is_bracket(x):
                converted_exp += ' '
                if x == '(':
                    stk.push(x)
                else:
                    while stk.top() and stk.top() != '(':
                        converted_exp += stk.pop() + ' '
                    stk.pop()
            elif self.__is_extract(x):
                converted_exp += ' '
                if x == '[':
                    stk.push(x)
                elif x == ':':
                    while stk.top() and stk.top() != '[':
                        converted_exp += stk.pop() + ' '
                    stk.push(x)
                else:
                    while stk.top() and stk.top() != '[':
                        converted_exp += stk.pop() + ' '
                    stk.pop()

            elif self.__is_variable(x):
                converted_exp += x

            elif x=="=":
                converted_exp += ' '
                stk.push("=")

            elif x=="\n":
                while stk.top() and stk.top() != '=':
                        converted_exp += stk.pop() + ' '
                stk.pop()

        # pop all the operators
        while stk.top():
            converted_exp += ' ' + stk.pop() + ' '
        return converted_exp
    def __get_result(self, operand_2, operand_1, operator):
        if operator == '+':
            return operand_1 + operand_2
        elif operator == '-':
            return operand_1 - operand_2
        elif operator == '*':
            return operand_1 * operand_2
        elif operator == '/':
            if operand_2 != 0:
                return operand_1 / operand_2
            else:
                print('Error: {}: divisor cannot be zero'.format(self.__exp))
                return None
    def __calc_postfix_exp(self, exp):
        """
        Get the result from a converted postfix expression
        e.g. 6 5 2 3 + 8 * + 3 + *
        :return: result
        """
        assert isinstance(exp, str)
        stk = Stack()
        exp_split = exp.strip().split()
        for x in exp_split:
            if self.__is_operators(x):
                # pop two top numbers in the stack
                r = self.__get_result(stk.pop(), stk.pop(), x)
                if r is None:
                    return None
                else:
                    stk.push(r)
            else:
                # push the converted number to the stack
                stk.push(float(x))
        return stk.pop()
    def __calc(self):
        """
        Try to get the result of the expression
        :return: None or result
        """
        # Validate
        if self.__validate():
            # Convert, then run the algorithm to get the result
            return self.__convert2postfix_exp()
            #return self.__calc_postfix_exp(self.__convert2postfix_exp())
        else:
            return None
    def get_result(self, expression):
        """
        Get the result of an expression
        Suppose we have got a valid expression
        :return: None or result
        """
        self.__exp = expression.replace(":=", "=").split("\n")

        op = Stack()
        data = Stack()
        Soc = data
        index=0
        while index<len(self.__exp):
            exp=self.__exp[index].strip()
            index+=1
            grammar = re.match("FOR (?P<EXP1>[:=+\(\)_\w ]*) to (?P<EXP2>[:=+\(\)_\w ]*)\w*", exp)
            IF = re.match("IF (?P<EXP1>[:=+\(\)_\w ]*)", exp)
            if grammar:
                gd = grammar.groupdict()
                op.push("FOR")
                data.push(Stack())
                Soc = Soc.top()
                # Soc.push(Calculator().get_result(gd["EXP1"]))
                # Soc.push(Calculator().get_result(gd["EXP2"]))
                Soc.push("FOR")
                Soc.push(Calculator().get_result(gd["EXP1"]))
                Soc.push(Calculator().get_result(gd["EXP2"]))
                continue
            elif IF:
                gd = IF.groupdict()
                op.push("IF")
                data.push(Stack())
                Soc = Soc.top()
                Soc.push("IF")
                Soc.push(self.__convert2postfix_exp(gd["EXP1"]))
                continue

            if exp in "\n\t ":
                continue
            elif self.__is_grammar(exp):
                stop = None
                if exp=="ENDFOR":
                    stop = 'FOR'
                elif exp=="FI":
                    stop = 'IF'
                else:
                    raise Exception("????")
                if op.top()==None:
                    return data
                while op.top() and op.top() != stop:
                    data.push(op.pop())
                data.push([op.pop(), Soc.get(), Soc1.get()])
                Soc = Stack()
                Soc1 = Stack()
            else:
                if self.__is_grammar(op.top()):
                    res = self.__convert2postfix_exp(exp)
                    data.top().push(res)
                else:
                    data.push(self.__convert2postfix_exp(exp))
        # while Soc.top():
        #     data.push(Soc.pop())
        return data

        #return self.__calc()
    """
    Utilities
    """
    @staticmethod
    def __is_operators(x):
        return x in ['+', '-', '*', '/']
    @staticmethod
    def __is_bracket(x):
        return x in ['(', ')']
    @staticmethod
    def __is_extract(x):
        return x in ['[', ']', ":"]
    @staticmethod
    def __is_method(x):
        for i in ['ABS',"AND", "OR", "XOR"]:
            if x.find(i)==0:
                return i
        return False

    @staticmethod
    def __is_variable(x):
        return (ord(x) >= ord("A") and ord(x)<=ord("Z")) or (ord(x) >= ord("a") and ord(x)<=ord("z"))
    @staticmethod
    def __is_digit(x):
        return x.isdigit()
    @staticmethod
    def __get_priority(op):
        if op in ['=']:
            return -2
        elif op in ['[', ']']:
            return -1
        elif op in ['+', '-']:
            return 0
        elif op in ['*', '/']:
            return 1
    @staticmethod
    def __is_grammar(op):
        if op in ["FOR", "ENDFOR", "to","IF","FI"]:
            return True
        return False



class call:
    def __init__(self, insn):
        sig=insn.xpath('div[@class="signature"]/span[@class="sig"]')[0]
        self.instruction=None
        for dynopsis in insn.xpath('div[@class="details"]/div[@class="synopsis"]/text()'):
            if "Instruction" in dynopsis:
                self.instruction=dynopsis.replace("Instruction: ","")
        self.cpuid=insn.xpath('div[@class="details"]/div[@class="synopsis"]/span[@class="cpuid"]/text()')[0]
        self.name = sig.xpath('span[@class="name"]/text()')[0]
        rety=sig.xpath('span[@class="rettype"]/text()')
        self.rettype =rety[0] if rety else ""
        params = sig.xpath('span[starts-with(@class,"param")]')
        self.params=[]
        for ind in range(0,len(params),2):
            p1=params[ind].xpath("text()")[0]
            if p1=="void":
                self.params.append("void")
                break
            p2=params[ind+1].xpath("text()")[0]
            self.params.append([p1,p2])
        description=insn.xpath('div[@class="details"]/div[@class="description"]/node()')
        self.description="\n"
        for des in description:
            if not isinstance(des,str):
                t=des.xpath('text()')
                if t:
                    des="["+t[0]+"]"
                else:
                    des=""
            self.description=self.description+des
        operation=insn.xpath('div[@class="details"]/div[@class="operation"]/text()')
        self.operation="\n"+operation[0] if operation else None
    def __str__(self):
        res=""
        for i in self.__dict__:
            res = res + "{:s}\t{:s}\n".format(str(i),str(self.__dict__[i]))
        return res
intrinsics={}
tree = etree.HTML(html)
intrinsics_list=tree.xpath('//div[@id="intrinsics_list"]/div')


code = """
YMM0[MAX:0] := 0
YMM1[MAX:0] := 0
IF _64_BIT_MODE
	YMM8[MAX:0] := 0
	FOR j := 0 to 15
        i := j*16
        dst[i+15:i] := ABS(a[i+15:i])
    ENDFOR
    dst[MAX:256] := 0
	YMM13[MAX:0] := 0
FI
"""
ca=Calculator()
res = ca.get_result(code)
print(res)

for insn in intrinsics_list:
    kind=insn.xpath('@class')
    cf=call(insn)
    ca = Calculator()
    code = cf.operation
    if code:
        try:
            data = ca.get_result(code)
            intrinsics[cf.name] = [cf, data]
            print (cf.name,data )
        except Exception as e:
            print(e)
    else:
        intrinsics[cf.name] = [cf, None]




print(intrinsics)
