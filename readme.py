#!/usr/bin/env python3

"""
Check Lisp examples in README.md.

To run:

    pip3 install -r requirements.txt
    ./readme.py

The return code is zero iff all Lisp examples in the README run without
errors in an SBCL REPL and their outputs match the given outputs. Such
output can be specified in a language-less code block immediately
following the Lisp code block.

The whole REPL session is printed to stdout. If the REPL session exits
unexpectedly, or any evaluation takes longer than one second, or an
error occurs, or the output doesn't match, then a descriptive error
message is printed to stderr and an exit code of 1 is returned.
"""

import pathlib
import sys

import marko.block as block
import marko.ext.gfm as gfm
import pexpect


def pairwise(things):
    """Return a list of pairs of adjacent elements from things.

    The last element of this list is the pair (things[-1], None)."""
    return zip(things, things[1:] + [None])


def is_code_block(element):
    """Return truthy iff the Marko element is a code block."""
    types = [block.CodeBlock, block.FencedCode]
    return any(isinstance(element, t) for t in types)


def code_block_to_dict(code_block):
    """Return a dict of the lang and text of the Marko code block."""
    return {
        'lang': code_block.lang,
        # should only have one child but just in case; also, children of
        # the child is just a string holding the text
        'text': ''.join(child.children for child in code_block.children),
    }


def lisp_examples(element):
    """Return a list of all Lisp examples in the Marko element.

    A Lisp example is a code block whose language is 'lisp', and is
    returned as a dictionary whose key 'code' holds the text of that
    code block. If the Lisp code block is immediately followed by
    another code block whose language is the empty string, then the text
    of that second block is also included in the dictionary, under the
    key 'output'."""
    examples = []
    if hasattr(element, 'children'):
        children = element.children
        # sometimes the children are just a string holding the text
        if isinstance(children, list):
            for a, b in pairwise(children):
                if is_code_block(a):
                    code = code_block_to_dict(a)
                    if code['lang'] == 'lisp':
                        example = {'code': code['text']}
                        if is_code_block(b):
                            output = code_block_to_dict(b)
                            if not output['lang']:
                                example['output'] = output['text']
                        examples.append(example)
                else:
                    # will safely skip when a has no grandchildren
                    examples.extend(lisp_examples(a))
    return examples


def slurp(filename):
    """Return the contents of filename as a string."""
    with open(filename) as file:
        return file.read()


examples = lisp_examples(gfm.gfm.parse(slurp('README.md')))
# Quicklisp isn't present by default in a raw SBCL in the Docker image,
# but it is installed already so we just need to load it
args = ['--load', f'{pathlib.Path.home()}/quicklisp/setup.lisp']
# having echo would mean we have to strip the input code out of
# repl.before; each code example must take less than one second, so that
# when there's an error we only have to wait one second; encoding must
# be set so that repl.before doesn't return binary strings
repl = pexpect.spawn('sbcl', args, echo=False, timeout=1, encoding='utf-8')
repl.logfile = sys.stdout
# regex matching the default SBCL prompt
prompt = r'\* '
# possibilities when we eval
patterns = [prompt, pexpect.EOF, pexpect.TIMEOUT]
# nothing should go wrong before we eval anything
repl.expect(prompt)
for example in examples:
    code = example['code']
    repl.send(code)
    index = repl.expect(patterns)
    if index == patterns.index(pexpect.EOF):
        sys.exit('Exited REPL unexpectedly.')
    elif index == patterns.index(pexpect.TIMEOUT):
        # the error is shown in the log to stdout
        sys.exit('Timeout: either took too long or an error occurred.')
    if 'output' in example:
        expected = example['output']
        # Pexpect returns CR/LF
        actual = repl.before.replace('\r\n', '\n')
        if expected != actual:
            # the actual output is shown in the log to stdout
            sys.exit(f'Expected:\n\n{expected}')
repl.sendline('(cl-user::quit)')
