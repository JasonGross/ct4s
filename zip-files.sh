#!/bin/bash
coq_makefile *.v > Makefile
make html
python make-index.py
zip jasonssubmissions.zip html/ html/* *.v index.html Makefile 2013*.pdf
