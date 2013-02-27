#!/usr/bin/python
from __future__ import with_statement
import os, sys, glob, re

def get_sorted_exercise_v_list():
    exercises = glob.glob('Exercise_*.v')
    reg = re.compile('Exercise_([0-9]+)_([0-9]+)_([0-9]+)_([0-9]+).v')
    exercises = list(sorted([tuple(map(int, reg.findall(sec)[0])) for sec in exercises]))
    return [('Exercise %d.%d.%d.%d' % sec,
             'Exercise_%d_%d_%d_%d.v' % sec) for sec in exercises]

def get_sorted_exercise_html_list():
    return [(name, 'html/' + url[:-2] + '.html') for name, url in get_sorted_exercise_v_list()]

def get_sorted_v_list():
    return [(i, i) for i in sorted(glob.glob('*.v'))]

def get_sorted_v_html_list():
    return [(name, 'html/' + url[:-2] + '.html') for name, url in get_sorted_v_list()]

def get_sorted_pset_list():
    psets = glob.glob('*Problem Set*.pdf')
    reg = re.compile('Problem Set [0-9]+')
    return list(sorted((reg.findall(pset)[0], pset) for pset in psets))

def make_page():
    html = r"""<html>
<head>
<title>Jason Gross' Exercises, Problem Set Solutions, and Coq Code</title>
</head>
<body>"""
    html += """
<h1>Coq Code</h1>
<a href="html/index.html">Index of Coq Code</a><br>
<h2>Exercises</h2>
<ul>
"""
    for (namev, urlv), (nameh, urlh) in zip(get_sorted_exercise_v_list(), get_sorted_exercise_html_list()):
        if namev != nameh: print('Error: name mismatch (%s, %s)' % (repr(nameh), repr(namev)))
        html += '<li>%s <a href="%s">[html]</a> <a href="%s">[Coq file]</a></li>\n' % (namev, urlh, urlv)
    html += """
</ul>
<h2>Supporting Coq Code</h2>
<ul>
"""
    for (namev, urlv), (nameh, urlh) in zip(get_sorted_v_list(), get_sorted_v_html_list()):
        if namev[:len('Exercise_')] != 'Exercise_':
            if namev != nameh: print('Error: name mismatch (%s, %s)' % (repr(nameh), repr(namev)))
            html += '<li>%s <a href="%s">[html]</a> <a href="%s">[Coq file]</a></li>\n' % (namev, urlh, urlv)
    html += """
</ul>
<h1>Full Problem Sets</h1>
<ul>
"""
    for name, url in get_sorted_pset_list():
        html += '<li><a href="%s">%s</a></li>\n' % (url, name)
    html += """
</ul>
</body>
</html>"""
    return html

if __name__ == '__main__' :
    html = make_page()
    with open('index.html', 'w') as f:
        f.write(html)
