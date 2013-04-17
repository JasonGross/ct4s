from __future__ import with_statement
import os, subprocess, re

file_contents = {}
file_imports = {}

def get_file(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    if file_name not in file_contents.keys():
        print(file_name)
        try:
            with open(file_name, 'r', encoding='UTF-8') as f:
                file_contents[file_name] = f.read()
        except TypeError:
            with open(file_name, 'r') as f:
                file_contents[file_name] = f.read()
    return file_contents[file_name]

def get_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    if file_name not in file_imports.keys():
        lines = get_file(file_name).split('\n')
        import_lines = [i.strip('. ') for i in lines if
                        i.strip()[:len('Require ')] == 'Require ' or
                        i.strip()[:len('Import ')] == 'Import ']
        imports = set((' ' + ' '.join(import_lines)).replace(' Require ', ' ').replace(' Import ', ' ').replace(' Export ', ' ').strip().split(' '))
        file_imports[file_name] = tuple(sorted(imports))
    return file_imports[file_name]

def merge_imports(*imports):
    rtn = []
    for import_list in imports:
        for i in import_list:
            if i not in rtn:
                rtn.append(i)
    return rtn

def recursively_get_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    if os.path.exists(file_name):
        imports = get_imports(file_name)
        imports_list = [recursively_get_imports(i) for i in imports]
        return merge_imports(*imports_list) + [file_name[:-2]]
    return [file_name[:-2]]

def contents_without_imports(file_name):
    if file_name[-2:] != '.v': file_name += '.v'
    contents = get_file(file_name)
    lines = [i for i in contents.split('\n') if
             i.strip()[:len('Require ')] != 'Require ' and
             i.strip()[:len('Import ')] != 'Import ' and
             i.strip() not in ('Set Implicit Arguments.', 'Generalizable All Variables.')]
    return '\n'.join(lines)

def filter_printings(contents):
    lines = contents.split('\n')
    commented_printings = [line for line in lines if line[:len('(* printing ')] == '(* printing ']
    printings = [line for line in lines if line[:len('(** printing ')] == '(** printing ']
    rtn = (# list(sorted(set(commented_printings))) +
           list(sorted(set(printings))) + 
           [line for line in lines if
            (line[:len('(* printing ')] != '(* printing '
             and line[:len('(** printing ')] != '(** printing ')])
    return '\n'.join(rtn)

def make_file_list(*file_names):
    rtn = []
    file_names = [file_name if (file_name[-2:] != '.v') else file_name[:-2]
                  for file_name in file_names]
    for file_name in file_names:
        rtn += recursively_get_imports(file_name + '.v')
    all_imports = []
    print('file names in order:')
    for i in rtn:
        if i not in all_imports and i not in file_names:
            print(i)
            all_imports.append(i)
    return all_imports + list(file_names)

def include_imports(*file_names):
    all_imports = make_file_list(*file_names)
    remaining_imports = []
    rtn = ''
    for import_name in all_imports:
        if os.path.exists(import_name + '.v'):
            rtn += contents_without_imports(import_name)
        else:
            remaining_imports.append(import_name)
    rtn = 'Require Import %s.\n\nSet Implicit Arguments.\n\nGeneralizable All Variables.\n\n%s' % (' '.join(remaining_imports), rtn)
    return filter_printings(rtn)

def build_pset(pset_n, *file_names):
    global file_contents
    global file_imports
    file_contents = {}
    file_imports = {}
    reg = re.compile('^Exercise_([0-9]+)_([0-9]+)_([0-9]+)_([0-9]+)(?:.v)?$')
    extra_file_names = [i for i in file_names if reg.match(i) is None]
    file_name_data = sorted(tuple(map(int, reg.match(i).groups())) for i in file_names if reg.match(i) is not None)
    file_names = extra_file_names + ['Exercise_%d_%d_%d_%d.v' % i for i in file_name_data]
    rtn = include_imports(*file_names)
    lines = rtn.split('\n')
    printings = '\n'.join([i for i in lines if i[:len('(** printing ')] == '(** printing '])
    rest = '\n'.join([i for i in lines if i[:len('(** printing ')] != '(** printing '])
    with open('../Homework%d.v' % pset_n, 'w') as f:
        f.write(printings)
        f.write("\n\n(** * Homework %d, By Jason Gross *)\n\n" % pset_n)
        f.write(rest)
    p = subprocess.Popen(['coqc', '-q', '-I', '.', 'Homework%d' % pset_n],
                         cwd=os.path.abspath('../'),
                         stderr=subprocess.PIPE,
                         stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    if stdout:
        print('Out:')
        print(stdout)
    if stderr:
        print('Error:')
        print(stderr)
    p = subprocess.Popen(['coqdoc', '--utf8', '--html', 'Homework%d.v' % pset_n],
                         cwd=os.path.abspath('../'),
                         stderr=subprocess.PIPE,
                         stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    if stdout:
        print('Out:')
        print(stdout)
    if stderr:
        print('Error:')
        print(stderr)
                    
        
# build_pset(6, 'Exercise_4_1_2_29.v', 'Exercise_4_1_2_28.v', 'Exercise_4_1_2_30.v', 'Exercise_4_1_2_31.v', 'Exercise_4_2_1_10.v', 'Exercise_4_2_1_13.v', 'Exercise_4_2_1_14.v', 'Exercise_4_2_1_16.v', 'Exercise_4_2_3_2.v', 'Exercise_4_2_3_12.v', 'Exercise_4_2_4_3.v', 'Exercise_4_2_4_4.v')
os.chdir(r'D:\Documents\Dropbox\MIT\2012-2013\18.S996 Category theory for scientists\jasonssubmissions')
# build_pset(7, 'Exercise_4_3_1_10.v', 'Exercise_4_3_1_3.v', 'Exercise_4_3_1_9.v', 'Exercise_4_3_2_5.v', 'Exercise_4_4_1_1.v', 'Exercise_4_4_1_5.v', 'Exercise_4_4_1_6.v', 'Exercise_4_4_1_7.v', 'Exercise_4_5_1_14.v', 'Exercise_4_5_1_16.v', 'Exercise_4_5_1_28.v', 'Exercise_4_5_1_4.v')
# build_pset(8, 'Exercise_4_5_2_12.v', 'Exercise_4_5_2_3.v', 'Exercise_4_5_2_5.v', 'Exercise_4_5_2_9.v', 'Exercise_4_5_3_11.v', 'Exercise_4_5_3_13.v', 'Exercise_4_5_3_6.v', 'Exercise_4_5_3_8.v')
build_pset(9, 'Exercise_4_6_1_5.v', 'Exercise_4_6_4_3.v', 'Exercise_5_1_1_6.v', 'Exercise_4_6_2_4.v', 'Exercise_5_1_1_3.v', 'Exercise_5_1_1_9.v')
