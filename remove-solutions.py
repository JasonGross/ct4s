#!/usr/bin/env python
from __future__ import with_statement
import os, sys, re


def get_file(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    try:
        with open(file_name, 'r', encoding='UTF-8') as f:
            return f.read()
    except TypeError:
        with open(file_name, 'r') as f:
            return f.read()


def put_file(file_name, text):
    if file_name[-2:] != '.v': file_name += '.v'
    try:
        with open(file_name, 'w', encoding='UTF-8') as f:
            f.write(text)
    except TypeError:
        with open(file_name, 'w') as f:
            f.write(text)


def remove_solutions(file_name):
    text = get_file(file_name)
    blocks = re.split(r'\s+\(\*\* \*+ Solution \*\)', text)
    if len(blocks) > 0:
        first, rest = blocks[0], [re.sub(r'\s+\(\*\*\s+[^-\*].*?\*\)', '', i, flags=re.DOTALL)
                                  for i in blocks[1:]]
        put_file(file_name, first + ''.join(rest))

if __name__ == '__main__':
    for i in sys.argv[1:]:
        print('Removing solutions from %s' % i)
        remove_solutions(i)
        
