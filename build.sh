#!/bin/sh

sbcl --end-runtime-options --disable-debugger \
    --eval '(defvar *save-executable* t)' \
    --load main.lisp
